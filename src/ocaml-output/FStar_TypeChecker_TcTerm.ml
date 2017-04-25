open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___91_4 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___91_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___91_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___91_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___91_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___91_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___91_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___91_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___91_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___91_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___91_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___91_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___91_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___91_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___91_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___91_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___91_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___91_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___91_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___91_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___91_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___91_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___91_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___91_4.FStar_TypeChecker_Env.qname_and_index)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___92_8 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___92_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___92_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___92_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___92_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___92_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___92_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___92_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___92_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___92_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___92_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___92_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___92_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___92_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___92_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___92_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___92_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___92_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___92_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___92_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___92_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___92_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___92_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___92_8.FStar_TypeChecker_Env.qname_and_index)
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
  fun uu___85_47  ->
    match uu___85_47 with
    | Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____49 -> false
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
            | uu____94 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____100 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____100 with
                 | None  -> t1
                 | Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____108 =
                          let msg =
                            match head_opt with
                            | None  ->
                                let uu____110 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____110
                            | Some head1 ->
                                let uu____112 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____113 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____112 uu____113 in
                          let uu____114 =
                            let uu____115 =
                              let uu____118 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____118) in
                            FStar_Errors.Error uu____115 in
                          Prims.raise uu____114 in
                        let s =
                          let uu____120 =
                            let uu____121 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left Prims.fst uu____121 in
                          FStar_TypeChecker_Util.new_uvar env uu____120 in
                        let uu____126 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____126 with
                        | Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____130 -> fail ())) in
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
        let uu____161 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____161
        then s
        else (FStar_Syntax_Syntax.NT ((Prims.fst b), v1)) :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___93_175 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___93_175.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___93_175.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____176  ->
             let uu____177 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____177 t)
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
            let uu____216 =
              let uu____217 = FStar_Syntax_Subst.compress t in
              uu____217.FStar_Syntax_Syntax.n in
            match uu____216 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____220,c) ->
                let uu____232 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____232
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____234 =
                    let uu____235 = FStar_Syntax_Subst.compress t1 in
                    uu____235.FStar_Syntax_Syntax.n in
                  (match uu____234 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____239 -> false
                   | uu____240 -> true)
                else false
            | uu____242 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____245 =
                  let uu____248 =
                    (let uu____249 = should_return t in
                     Prims.op_Negation uu____249) ||
                      (let uu____250 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____250) in
                  if uu____248
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____245
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____258 =
            let uu____262 = FStar_TypeChecker_Env.expected_typ env in
            match uu____262 with
            | None  -> let uu____267 = memo_tk e t in (uu____267, lc, guard)
            | Some t' ->
                ((let uu____270 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____270
                  then
                    let uu____271 = FStar_Syntax_Print.term_to_string t in
                    let uu____272 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____271
                      uu____272
                  else ());
                 (let uu____274 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____274 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____285 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____285 with
                       | (e2,g) ->
                           ((let uu____294 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____294
                             then
                               let uu____295 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____296 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____297 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____298 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____295 uu____296 uu____297 uu____298
                             else ());
                            (let msg =
                               let uu____304 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____304
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_28  -> Some _0_28)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____319 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____319 with
                             | (lc2,g2) ->
                                 let uu____327 = memo_tk e2 t' in
                                 (uu____327, (set_lcomp_result lc2 t'), g2)))))) in
          match uu____258 with
          | (e1,lc1,g) ->
              ((let uu____335 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____335
                then
                  let uu____336 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____336
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
        let uu____353 = FStar_TypeChecker_Env.expected_typ env in
        match uu____353 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____359 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____359 with
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
      fun uu____381  ->
        match uu____381 with
        | (e,c) ->
            let expected_c_opt =
              match copt with
              | Some uu____396 -> copt
              | None  ->
                  let uu____397 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Syntax_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____398 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____398)) in
                  if uu____397
                  then
                    let uu____400 =
                      FStar_Syntax_Util.ml_comp
                        (FStar_Syntax_Util.comp_result c)
                        e.FStar_Syntax_Syntax.pos in
                    Some uu____400
                  else
                    (let uu____402 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____402
                     then None
                     else
                       (let uu____405 = FStar_Syntax_Util.is_pure_comp c in
                        if uu____405
                        then
                          let uu____407 =
                            FStar_Syntax_Syntax.mk_Total
                              (FStar_Syntax_Util.comp_result c) in
                          Some uu____407
                        else
                          (let uu____409 =
                             FStar_Syntax_Util.is_pure_or_ghost_comp c in
                           if uu____409
                           then
                             let uu____411 =
                               FStar_Syntax_Syntax.mk_GTotal
                                 (FStar_Syntax_Util.comp_result c) in
                             Some uu____411
                           else None))) in
            (match expected_c_opt with
             | None  ->
                 let uu____416 = norm_c env c in
                 (e, uu____416, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____419 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low in
                   if uu____419
                   then
                     let uu____420 = FStar_Syntax_Print.term_to_string e in
                     let uu____421 = FStar_Syntax_Print.comp_to_string c in
                     let uu____422 =
                       FStar_Syntax_Print.comp_to_string expected_c in
                     FStar_Util.print3
                       "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                       uu____420 uu____421 uu____422
                   else ());
                  (let c1 = norm_c env c in
                   (let uu____426 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low in
                    if uu____426
                    then
                      let uu____427 = FStar_Syntax_Print.term_to_string e in
                      let uu____428 = FStar_Syntax_Print.comp_to_string c1 in
                      let uu____429 =
                        FStar_Syntax_Print.comp_to_string expected_c in
                      FStar_Util.print3
                        "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                        uu____427 uu____428 uu____429
                    else ());
                   (let uu____431 =
                      FStar_TypeChecker_Util.check_comp env e c1 expected_c in
                    match uu____431 with
                    | (e1,uu____439,g) ->
                        let g1 =
                          let uu____442 = FStar_TypeChecker_Env.get_range env in
                          FStar_TypeChecker_Util.label_guard uu____442
                            "could not prove post-condition" g in
                        ((let uu____444 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low in
                          if uu____444
                          then
                            let uu____445 =
                              FStar_Range.string_of_range
                                e1.FStar_Syntax_Syntax.pos in
                            let uu____446 =
                              FStar_TypeChecker_Rel.guard_to_string env g1 in
                            FStar_Util.print2
                              "(%s) DONE check_expected_effect; guard is: %s\n"
                              uu____445 uu____446
                          else ());
                         (let e2 =
                            FStar_TypeChecker_Util.maybe_lift env e1
                              (FStar_Syntax_Util.comp_effect_name c1)
                              (FStar_Syntax_Util.comp_effect_name expected_c)
                              (FStar_Syntax_Util.comp_result c1) in
                          (e2, expected_c, g1)))))))
let no_logical_guard env uu____468 =
  match uu____468 with
  | (te,kt,f) ->
      let uu____475 = FStar_TypeChecker_Rel.guard_form f in
      (match uu____475 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____480 =
             let uu____481 =
               let uu____484 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____485 = FStar_TypeChecker_Env.get_range env in
               (uu____484, uu____485) in
             FStar_Errors.Error uu____481 in
           Prims.raise uu____480)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____492 = FStar_TypeChecker_Env.expected_typ env in
    match uu____492 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____495 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____495
let check_smt_pat env t bs c =
  let uu____530 = FStar_Syntax_Util.is_smt_lemma t in
  if uu____530
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____531;
          FStar_Syntax_Syntax.effect_name = uu____532;
          FStar_Syntax_Syntax.result_typ = uu____533;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____537)::[];
          FStar_Syntax_Syntax.flags = uu____538;_}
        ->
        let pat_vars =
          let uu____572 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats in
          FStar_Syntax_Free.names uu____572 in
        let uu____573 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____585  ->
                  match uu____585 with
                  | (b,uu____589) ->
                      let uu____590 = FStar_Util.set_mem b pat_vars in
                      Prims.op_Negation uu____590)) in
        (match uu____573 with
         | None  -> ()
         | Some (x,uu____594) ->
             let uu____597 =
               let uu____598 = FStar_Syntax_Print.bv_to_string x in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____598 in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____597)
    | uu____599 -> failwith "Impossible"
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
        let uu____620 =
          let uu____621 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____621 in
        if uu____620
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___94_639 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___94_639.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___94_639.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___94_639.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___94_639.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___94_639.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___94_639.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___94_639.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___94_639.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___94_639.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___94_639.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___94_639.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___94_639.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___94_639.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___94_639.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___94_639.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___94_639.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___94_639.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___94_639.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___94_639.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___94_639.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___94_639.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___94_639.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___94_639.FStar_TypeChecker_Env.qname_and_index)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____662  ->
                           match uu____662 with
                           | (b,uu____667) ->
                               let t =
                                 let uu____669 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____669 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type _
                                  |FStar_Syntax_Syntax.Tm_arrow _ -> []
                                | uu____673 ->
                                    let uu____674 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____674]))) in
                 let as_lex_list dec =
                   let uu____679 = FStar_Syntax_Util.head_and_args dec in
                   match uu____679 with
                   | (head1,uu____690) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____706 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____709 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___86_713  ->
                           match uu___86_713 with
                           | FStar_Syntax_Syntax.DECREASES uu____714 -> true
                           | uu____717 -> false)) in
                 match uu____709 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____721 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____727 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____739 =
                 match uu____739 with
                 | (l,t) ->
                     let uu____748 =
                       let uu____749 = FStar_Syntax_Subst.compress t in
                       uu____749.FStar_Syntax_Syntax.n in
                     (match uu____748 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____782  ->
                                    match uu____782 with
                                    | (x,imp) ->
                                        let uu____789 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____789
                                        then
                                          let uu____792 =
                                            let uu____793 =
                                              let uu____795 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              Some uu____795 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____793
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____792, imp)
                                        else (x, imp))) in
                          let uu____797 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____797 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____810 =
                                   let uu____811 =
                                     let uu____812 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____813 =
                                       let uu____815 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____815] in
                                     uu____812 :: uu____813 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____811 in
                                 uu____810 None r in
                               let uu____820 = FStar_Util.prefix formals2 in
                               (match uu____820 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___95_846 = last1 in
                                      let uu____847 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___95_846.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___95_846.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____847
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____864 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____864
                                      then
                                        let uu____865 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____866 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____867 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____865 uu____866 uu____867
                                      else ());
                                     (l, t'))))
                      | uu____871 ->
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
        (let uu___96_1143 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___96_1143.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___96_1143.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___96_1143.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___96_1143.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___96_1143.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___96_1143.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___96_1143.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___96_1143.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___96_1143.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___96_1143.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___96_1143.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___96_1143.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___96_1143.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___96_1143.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___96_1143.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___96_1143.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___96_1143.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___96_1143.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___96_1143.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___96_1143.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___96_1143.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___96_1143.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___96_1143.FStar_TypeChecker_Env.qname_and_index)
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
      (let uu____1152 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1152
       then
         let uu____1153 =
           let uu____1154 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1154 in
         let uu____1155 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1153 uu____1155
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1161 -> failwith "Impossible"
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
           let uu____1200 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1200 with
            | (e2,c,g) ->
                let g1 =
                  let uu___97_1211 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___97_1211.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___97_1211.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___97_1211.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1224 = FStar_Syntax_Util.type_u () in
           (match uu____1224 with
            | (t,u) ->
                let uu____1232 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1232 with
                 | (e2,c,g) ->
                     let uu____1242 =
                       let uu____1251 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1251 with
                       | (env2,uu____1264) -> tc_pats env2 pats in
                     (match uu____1242 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___98_1285 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___98_1285.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___98_1285.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___98_1285.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1286 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1297 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1286, c, uu____1297))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1305 =
             let uu____1306 = FStar_Syntax_Subst.compress e1 in
             uu____1306.FStar_Syntax_Syntax.n in
           (match uu____1305 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1312,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1314;
                               FStar_Syntax_Syntax.lbtyp = uu____1315;
                               FStar_Syntax_Syntax.lbeff = uu____1316;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1334 =
                  let uu____1338 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1338 e11 in
                (match uu____1334 with
                 | (e12,c1,g1) ->
                     let uu____1345 = tc_term env1 e2 in
                     (match uu____1345 with
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
                            let uu____1362 =
                              let uu____1365 =
                                let uu____1366 =
                                  let uu____1374 =
                                    let uu____1378 =
                                      let uu____1380 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1380] in
                                    (false, uu____1378) in
                                  (uu____1374, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1366 in
                              FStar_Syntax_Syntax.mk uu____1365 in
                            uu____1362
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
                          let uu____1410 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1410)))
            | uu____1413 ->
                let uu____1414 = tc_term env1 e1 in
                (match uu____1414 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1438) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1453 = tc_term env1 e1 in
           (match uu____1453 with
            | (e2,c,g) ->
                let e3 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1479) ->
           let uu____1515 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1515 with
            | (env0,uu____1523) ->
                let uu____1526 = tc_comp env0 expected_c in
                (match uu____1526 with
                 | (expected_c1,uu____1534,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1539 =
                       let uu____1543 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1543 e1 in
                     (match uu____1539 with
                      | (e2,c',g') ->
                          let uu____1550 =
                            let uu____1554 =
                              let uu____1557 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____1557) in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1554 in
                          (match uu____1550 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 (FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_ascribed
                                       (e3, ((FStar_Util.Inl t_res), None),
                                         (Some
                                            (FStar_Syntax_Util.comp_effect_name
                                               expected_c2)))))
                                   (Some (t_res.FStar_Syntax_Syntax.n))
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2 in
                               let f =
                                 let uu____1608 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1608 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | None  -> f
                                 | Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic) in
                               let uu____1613 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1613 with
                                | (e5,c,f2) ->
                                    let uu____1623 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____1623))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1627) ->
           let uu____1663 = FStar_Syntax_Util.type_u () in
           (match uu____1663 with
            | (k,u) ->
                let uu____1671 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1671 with
                 | (t1,uu____1679,f) ->
                     let uu____1681 =
                       let uu____1685 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1685 e1 in
                     (match uu____1681 with
                      | (e2,c,g) ->
                          let uu____1692 =
                            let uu____1695 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1698  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1695 e2 c f in
                          (match uu____1692 with
                           | (c1,f1) ->
                               let uu____1704 =
                                 let uu____1708 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, ((FStar_Util.Inl t1), None),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____1708 c1 in
                               (match uu____1704 with
                                | (e3,c2,f2) ->
                                    let uu____1744 =
                                      let uu____1745 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1745 in
                                    (e3, c2, uu____1744))))))
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
           let uu____1822 = FStar_Syntax_Util.head_and_args top in
           (match uu____1822 with
            | (unary_op,uu____1836) ->
                let head1 =
                  let uu____1854 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (Prims.fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1854 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1898;
              FStar_Syntax_Syntax.pos = uu____1899;
              FStar_Syntax_Syntax.vars = uu____1900;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____1926 =
               let uu____1930 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____1930 with | (env0,uu____1938) -> tc_term env0 e1 in
             match uu____1926 with
             | (e2,c,g) ->
                 let uu____1947 = FStar_Syntax_Util.head_and_args top in
                 (match uu____1947 with
                  | (reify_op,uu____1961) ->
                      let u_c =
                        let uu____1977 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____1977 with
                        | (uu____1981,c',uu____1983) ->
                            let uu____1984 =
                              let uu____1985 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____1985.FStar_Syntax_Syntax.n in
                            (match uu____1984 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____1989 ->
                                 let uu____1990 = FStar_Syntax_Util.type_u () in
                                 (match uu____1990 with
                                  | (t,u) ->
                                      let g_opt =
                                        FStar_TypeChecker_Rel.try_teq true
                                          env1 c'.FStar_Syntax_Syntax.res_typ
                                          t in
                                      ((match g_opt with
                                        | Some g' ->
                                            FStar_TypeChecker_Rel.force_trivial_guard
                                              env1 g'
                                        | None  ->
                                            let uu____1999 =
                                              let uu____2000 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2001 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2002 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2000 uu____2001
                                                uu____2002 in
                                            failwith uu____1999);
                                       u))) in
                      let repr =
                        let uu____2004 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2004 u_c in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2026 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2026
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2027 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2027 with
                       | (e4,c2,g') ->
                           let uu____2037 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2037)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2039;
              FStar_Syntax_Syntax.pos = uu____2040;
              FStar_Syntax_Syntax.vars = uu____2041;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2073 =
               let uu____2074 =
                 let uu____2075 =
                   let uu____2078 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2078, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2075 in
               Prims.raise uu____2074 in
             let uu____2082 = FStar_Syntax_Util.head_and_args top in
             match uu____2082 with
             | (reflect_op,uu____2096) ->
                 let uu____2111 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2111 with
                  | None  -> no_reflect ()
                  | Some ed ->
                      let uu____2117 =
                        let uu____2118 =
                          FStar_All.pipe_right
                            ed.FStar_Syntax_Syntax.qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2118 in
                      if uu____2117
                      then no_reflect ()
                      else
                        (let uu____2124 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2124 with
                         | (env_no_ex,topt) ->
                             let uu____2135 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2150 =
                                   let uu____2153 =
                                     let uu____2154 =
                                       let uu____2164 =
                                         let uu____2166 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2167 =
                                           let uu____2169 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2169] in
                                         uu____2166 :: uu____2167 in
                                       (repr, uu____2164) in
                                     FStar_Syntax_Syntax.Tm_app uu____2154 in
                                   FStar_Syntax_Syntax.mk uu____2153 in
                                 uu____2150 None top.FStar_Syntax_Syntax.pos in
                               let uu____2179 =
                                 let uu____2183 =
                                   let uu____2184 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2184 Prims.fst in
                                 tc_tot_or_gtot_term uu____2183 t in
                               match uu____2179 with
                               | (t1,uu____2201,g) ->
                                   let uu____2203 =
                                     let uu____2204 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2204.FStar_Syntax_Syntax.n in
                                   (match uu____2203 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2215,(res,uu____2217)::
                                         (wp,uu____2219)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2253 -> failwith "Impossible") in
                             (match uu____2135 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2277 =
                                    let uu____2280 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2280 with
                                    | (e2,c,g) ->
                                        ((let uu____2290 =
                                            let uu____2291 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2291 in
                                          if uu____2290
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2297 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2297 with
                                          | None  ->
                                              ((let uu____2302 =
                                                  let uu____2306 =
                                                    let uu____2309 =
                                                      let uu____2310 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2311 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2310 uu____2311 in
                                                    (uu____2309,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2306] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2302);
                                               (let uu____2316 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2316)))
                                          | Some g' ->
                                              let uu____2318 =
                                                let uu____2319 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2319 in
                                              (e2, uu____2318))) in
                                  (match uu____2277 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2326 =
                                           let uu____2327 =
                                             let uu____2328 =
                                               let uu____2329 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2329] in
                                             let uu____2330 =
                                               let uu____2336 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2336] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2328;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2330;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2327 in
                                         FStar_All.pipe_right uu____2326
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e2, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2357 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2357 with
                                        | (e4,c1,g') ->
                                            let uu____2367 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2367))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2386 =
               let uu____2387 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2387 Prims.fst in
             FStar_All.pipe_right uu____2386 instantiate_both in
           ((let uu____2396 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2396
             then
               let uu____2397 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2398 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2397
                 uu____2398
             else ());
            (let uu____2400 = tc_term (no_inst env2) head1 in
             match uu____2400 with
             | (head2,chead,g_head) ->
                 let uu____2410 =
                   let uu____2414 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2414
                   then
                     let uu____2418 = FStar_TypeChecker_Env.expected_typ env0 in
                     check_short_circuit_args env2 head2 chead g_head args
                       uu____2418
                   else
                     (let uu____2421 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env2 head2 chead g_head args
                        uu____2421) in
                 (match uu____2410 with
                  | (e1,c,g) ->
                      ((let uu____2430 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2430
                        then
                          let uu____2431 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2431
                        else ());
                       (let c1 =
                          let uu____2434 =
                            ((FStar_TypeChecker_Env.should_verify env2) &&
                               (let uu____2435 =
                                  FStar_Syntax_Util.is_lcomp_partial_return c in
                                Prims.op_Negation uu____2435))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                          if uu____2434
                          then
                            FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                              env2 e1 c
                          else c in
                        let uu____2437 = comp_check_expected_typ env0 e1 c1 in
                        match uu____2437 with
                        | (e2,c2,g') ->
                            let gimp =
                              let uu____2448 =
                                let uu____2449 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2449.FStar_Syntax_Syntax.n in
                              match uu____2448 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2453) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c2.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___99_2485 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___99_2485.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___99_2485.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___99_2485.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2510 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2512 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2512 in
                            ((let uu____2514 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2514
                              then
                                let uu____2515 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2516 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2515 uu____2516
                              else ());
                             (e2, c2, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2546 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2546 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2558 = tc_term env12 e1 in
                (match uu____2558 with
                 | (e11,c1,g1) ->
                     let uu____2568 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2574 = FStar_Syntax_Util.type_u () in
                           (match uu____2574 with
                            | (k,uu____2580) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2582 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2582, res_t)) in
                     (match uu____2568 with
                      | (env_branches,res_t) ->
                          ((let uu____2589 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2589
                            then
                              let uu____2590 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2590
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2641 =
                              let uu____2644 =
                                FStar_List.fold_right
                                  (fun uu____2663  ->
                                     fun uu____2664  ->
                                       match (uu____2663, uu____2664) with
                                       | ((uu____2696,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2729 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____2729))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2644 with
                              | (cases,g) ->
                                  let uu____2750 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____2750, g) in
                            match uu____2641 with
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
                                           (fun uu____2803  ->
                                              match uu____2803 with
                                              | ((pat,wopt,br),uu____2819,lc,uu____2821)
                                                  ->
                                                  let uu____2828 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____2828))) in
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
                                            ((FStar_Util.Inl
                                                (cres.FStar_Syntax_Syntax.res_typ)),
                                              None),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.eff_name)))))
                                      None e3.FStar_Syntax_Syntax.pos in
                                  let uu____2884 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____2884
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____2891 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____2891 in
                                     let lb =
                                       let uu____2895 =
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
                                           uu____2895;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____2899 =
                                         let uu____2902 =
                                           let uu____2903 =
                                             let uu____2911 =
                                               let uu____2912 =
                                                 let uu____2913 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____2913] in
                                               FStar_Syntax_Subst.close
                                                 uu____2912 e_match in
                                             ((false, [lb]), uu____2911) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____2903 in
                                         FStar_Syntax_Syntax.mk uu____2902 in
                                       uu____2899
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____2927 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____2927
                                  then
                                    let uu____2928 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____2929 =
                                      let uu____2930 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____2930 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____2928 uu____2929
                                  else ());
                                 (let uu____2932 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____2932))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2935;
                FStar_Syntax_Syntax.lbunivs = uu____2936;
                FStar_Syntax_Syntax.lbtyp = uu____2937;
                FStar_Syntax_Syntax.lbeff = uu____2938;
                FStar_Syntax_Syntax.lbdef = uu____2939;_}::[]),uu____2940)
           ->
           ((let uu____2955 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____2955
             then
               let uu____2956 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____2956
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2958),uu____2959) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2969;
                FStar_Syntax_Syntax.lbunivs = uu____2970;
                FStar_Syntax_Syntax.lbtyp = uu____2971;
                FStar_Syntax_Syntax.lbeff = uu____2972;
                FStar_Syntax_Syntax.lbdef = uu____2973;_}::uu____2974),uu____2975)
           ->
           ((let uu____2991 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____2991
             then
               let uu____2992 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____2992
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____2994),uu____2995) ->
           check_inner_let_rec env1 top)
and tc_tactic_opt:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option ->
      FStar_Syntax_Syntax.term Prims.option
  =
  fun env  ->
    fun topt  ->
      match topt with
      | None  -> None
      | Some tactic ->
          let uu____3018 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3018 with
           | (tactic1,uu____3024,uu____3025) -> Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____3060 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3060 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3073 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3073
              then FStar_Util.Inl t1
              else
                (let uu____3077 =
                   let uu____3078 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3078 in
                 FStar_Util.Inr uu____3077) in
            let is_data_ctor uu___87_3087 =
              match uu___87_3087 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____3090 -> false in
            let uu____3092 =
              (is_data_ctor dc) &&
                (let uu____3093 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3093) in
            if uu____3092
            then
              let uu____3099 =
                let uu____3100 =
                  let uu____3103 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3106 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3103, uu____3106) in
                FStar_Errors.Error uu____3100 in
              Prims.raise uu____3099
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3117 =
            let uu____3118 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3118 in
          failwith uu____3117
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3137 =
              let uu____3138 = FStar_Syntax_Subst.compress t1 in
              uu____3138.FStar_Syntax_Syntax.n in
            match uu____3137 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3141 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3149 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___100_3169 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___100_3169.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___100_3169.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___100_3169.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3197 =
            let uu____3204 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3204 with
            | None  ->
                let uu____3212 = FStar_Syntax_Util.type_u () in
                (match uu____3212 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3197 with
           | (t,uu____3233,g0) ->
               let uu____3241 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3241 with
                | (e1,uu____3252,g1) ->
                    let uu____3260 =
                      let uu____3261 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3261
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3262 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3260, uu____3262)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3264 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3273 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3273)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3264 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___101_3287 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___101_3287.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___101_3287.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3290 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3290 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3303 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3303
                       then FStar_Util.Inl t1
                       else
                         (let uu____3307 =
                            let uu____3308 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3308 in
                          FStar_Util.Inr uu____3307) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3314;
             FStar_Syntax_Syntax.pos = uu____3315;
             FStar_Syntax_Syntax.vars = uu____3316;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3324 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3324 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3346 =
                     let uu____3347 =
                       let uu____3350 = FStar_TypeChecker_Env.get_range env1 in
                       ("Unexpected number of universe instantiations",
                         uu____3350) in
                     FStar_Errors.Error uu____3347 in
                   Prims.raise uu____3346)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____3358 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___102_3360 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___103_3361 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___103_3361.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___103_3361.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___102_3360.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___102_3360.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3377 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3377 us1 in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3389 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3389 with
           | ((us,t),range) ->
               ((let uu____3407 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3407
                 then
                   let uu____3408 =
                     let uu____3409 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3409 in
                   let uu____3410 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3411 = FStar_Range.string_of_range range in
                   let uu____3412 = FStar_Range.string_of_use_range range in
                   let uu____3413 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
                     uu____3408 uu____3410 uu____3411 uu____3412 uu____3413
                 else ());
                (let fv' =
                   let uu___104_3416 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___105_3417 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___105_3417.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___105_3417.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___104_3416.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___104_3416.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3433 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3433 us in
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
          let uu____3469 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3469 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3478 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3478 with
                | (env2,uu____3486) ->
                    let uu____3489 = tc_binders env2 bs1 in
                    (match uu____3489 with
                     | (bs2,env3,g,us) ->
                         let uu____3501 = tc_comp env3 c1 in
                         (match uu____3501 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___106_3514 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___106_3514.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___106_3514.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___106_3514.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____3535 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3535 in
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
          let uu____3570 =
            let uu____3573 =
              let uu____3574 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3574] in
            FStar_Syntax_Subst.open_term uu____3573 phi in
          (match uu____3570 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____3581 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3581 with
                | (env2,uu____3589) ->
                    let uu____3592 =
                      let uu____3599 = FStar_List.hd x1 in
                      tc_binder env2 uu____3599 in
                    (match uu____3592 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3616 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____3616
                           then
                             let uu____3617 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____3618 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____3619 =
                               FStar_Syntax_Print.bv_to_string (Prims.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3617 uu____3618 uu____3619
                           else ());
                          (let uu____3621 = FStar_Syntax_Util.type_u () in
                           match uu____3621 with
                           | (t_phi,uu____3628) ->
                               let uu____3629 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____3629 with
                                | (phi2,uu____3637,f2) ->
                                    let e1 =
                                      let uu___107_3642 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x2) phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___107_3642.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___107_3642.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___107_3642.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____3661 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3661 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3670) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____3695 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____3695
            then
              let uu____3696 =
                FStar_Syntax_Print.term_to_string
                  (let uu___108_3697 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___108_3697.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___108_3697.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___108_3697.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3696
            else ());
           (let uu____3716 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____3716 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3724 ->
          let uu____3725 =
            let uu____3726 = FStar_Syntax_Print.term_to_string top in
            let uu____3727 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3726
              uu____3727 in
          failwith uu____3725
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3733 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3734,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3740,Some uu____3741) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3749 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3753 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3754 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3755 ->
          FStar_TypeChecker_Common.t_range
      | uu____3756 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____3767) ->
          let uu____3774 = FStar_Syntax_Util.type_u () in
          (match uu____3774 with
           | (k,u) ->
               let uu____3782 = tc_check_tot_or_gtot_term env t k in
               (match uu____3782 with
                | (t1,uu____3790,g) ->
                    let uu____3792 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____3792, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3794) ->
          let uu____3801 = FStar_Syntax_Util.type_u () in
          (match uu____3801 with
           | (k,u) ->
               let uu____3809 = tc_check_tot_or_gtot_term env t k in
               (match uu____3809 with
                | (t1,uu____3817,g) ->
                    let uu____3819 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____3819, u, g)))
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
            let uu____3835 =
              let uu____3836 =
                let uu____3837 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____3837 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____3836 in
            uu____3835 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____3842 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____3842 with
           | (tc1,uu____3850,f) ->
               let uu____3852 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____3852 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____3882 =
                        let uu____3883 = FStar_Syntax_Subst.compress head3 in
                        uu____3883.FStar_Syntax_Syntax.n in
                      match uu____3882 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3886,us) -> us
                      | uu____3892 -> [] in
                    let uu____3893 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____3893 with
                     | (uu____3906,args1) ->
                         let uu____3922 =
                           let uu____3934 = FStar_List.hd args1 in
                           let uu____3943 = FStar_List.tl args1 in
                           (uu____3934, uu____3943) in
                         (match uu____3922 with
                          | (res,args2) ->
                              let uu____3985 =
                                let uu____3990 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___88_4000  ->
                                          match uu___88_4000 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4006 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4006 with
                                               | (env1,uu____4013) ->
                                                   let uu____4016 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4016 with
                                                    | (e1,uu____4023,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____3990
                                  FStar_List.unzip in
                              (match uu____3985 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (Prims.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___109_4046 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___109_4046.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (Prims.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___109_4046.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4050 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4050 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____4053 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4053))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4061 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4064 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4064
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4067 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4067
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4071 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4071 Prims.snd
         | uu____4076 -> aux u)
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
            let uu____4097 =
              let uu____4098 =
                let uu____4101 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4101, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4098 in
            Prims.raise uu____4097 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4155 bs2 bs_expected1 =
              match uu____4155 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             let uu____4252 =
                               let uu____4253 =
                                 let uu____4256 =
                                   let uu____4257 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4257 in
                                 let uu____4258 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4256, uu____4258) in
                               FStar_Errors.Error uu____4253 in
                             Prims.raise uu____4252
                         | uu____4259 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4263 =
                           let uu____4266 =
                             let uu____4267 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4267.FStar_Syntax_Syntax.n in
                           match uu____4266 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4272 ->
                               ((let uu____4274 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4274
                                 then
                                   let uu____4275 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4275
                                 else ());
                                (let uu____4277 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4277 with
                                 | (t,uu____4284,g1) ->
                                     let g2 =
                                       let uu____4287 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4288 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4287
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4288 in
                                     let g3 =
                                       let uu____4290 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4290 in
                                     (t, g3))) in
                         match uu____4263 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___110_4306 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___110_4306.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___110_4306.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4315 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4315 in
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
                  | uu____4417 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4421 = tc_binders env1 bs in
                  match uu____4421 with
                  | (bs1,envbody,g,uu____4442) ->
                      let uu____4443 =
                        let uu____4450 =
                          let uu____4451 = FStar_Syntax_Subst.compress body1 in
                          uu____4451.FStar_Syntax_Syntax.n in
                        match uu____4450 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4463) ->
                            let uu____4499 = tc_comp envbody c in
                            (match uu____4499 with
                             | (c1,uu____4510,g') ->
                                 let uu____4512 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4514 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), uu____4512, body1, uu____4514))
                        | uu____4517 -> (None, None, body1, g) in
                      (match uu____4443 with
                       | (copt,tacopt,body2,g1) ->
                           (None, bs1, [], copt, tacopt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____4576 =
                    let uu____4577 = FStar_Syntax_Subst.compress t2 in
                    uu____4577.FStar_Syntax_Syntax.n in
                  match uu____4576 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4610 -> failwith "Impossible");
                       (let uu____4614 = tc_binders env1 bs in
                        match uu____4614 with
                        | (bs1,envbody,g,uu____4636) ->
                            let uu____4637 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4637 with
                             | (envbody1,uu____4656) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4668) ->
                      let uu____4673 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____4673 with
                       | (uu____4702,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4742 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____4742 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____4805 c_expected2 =
                               match uu____4805 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____4866 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____4866)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____4883 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____4883 in
                                        let uu____4884 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____4884)
                                    | Some (FStar_Util.Inl more_bs) ->
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
                                               let uu____4925 =
                                                 check_binders env3 more_bs
                                                   bs_expected3 in
                                               (match uu____4925 with
                                                | (env4,bs',more1,guard',subst2)
                                                    ->
                                                    let uu____4952 =
                                                      let uu____4968 =
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          guard guard' in
                                                      (env4,
                                                        (FStar_List.append
                                                           bs2 bs'), more1,
                                                        uu____4968, subst2) in
                                                    handle_more uu____4952
                                                      c_expected3)
                                           | uu____4977 ->
                                               let uu____4978 =
                                                 let uu____4979 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____4979 in
                                               fail uu____4978 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____4995 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____4995 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___111_5033 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___111_5033.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___111_5033.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___111_5033.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___111_5033.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___111_5033.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___111_5033.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___111_5033.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___111_5033.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___111_5033.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___111_5033.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___111_5033.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___111_5033.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___111_5033.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___111_5033.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___111_5033.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___111_5033.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___111_5033.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___111_5033.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___111_5033.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___111_5033.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___111_5033.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___111_5033.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___111_5033.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5047  ->
                                     fun uu____5048  ->
                                       match (uu____5047, uu____5048) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5073 =
                                             let uu____5077 =
                                               let uu____5078 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5078 Prims.fst in
                                             tc_term uu____5077 t3 in
                                           (match uu____5073 with
                                            | (t4,uu____5090,uu____5091) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5098 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___112_5099
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___112_5099.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___112_5099.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5098 ::
                                                        letrec_binders
                                                  | uu____5100 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5103 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5103 with
                            | (envbody,bs1,g,c) ->
                                let uu____5135 =
                                  let uu____5139 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5139
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5135 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), None, envbody2, body1, g))))
                  | uu____5175 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5190 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5190
                      else
                        (let uu____5192 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5192 with
                         | (uu____5220,bs1,uu____5222,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, tacopt,
                               envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5247 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5247 with
          | (env1,topt) ->
              ((let uu____5259 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5259
                then
                  let uu____5260 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5260
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5264 = expected_function_typ1 env1 topt body in
                match uu____5264 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5299 =
                      tc_term
                        (let uu___113_5303 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___113_5303.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___113_5303.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___113_5303.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___113_5303.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___113_5303.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___113_5303.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___113_5303.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___113_5303.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___113_5303.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___113_5303.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___113_5303.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___113_5303.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___113_5303.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___113_5303.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___113_5303.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___113_5303.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___113_5303.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___113_5303.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___113_5303.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___113_5303.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___113_5303.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___113_5303.FStar_TypeChecker_Env.qname_and_index)
                         }) body1 in
                    (match uu____5299 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5312 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5312
                           then
                             let uu____5313 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5322 =
                               let uu____5323 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5323 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5313 uu____5322
                           else ());
                          (let uu____5325 =
                             let uu____5329 =
                               let uu____5332 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5332) in
                             check_expected_effect
                               (let uu___114_5337 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___114_5337.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___114_5337.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___114_5337.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___114_5337.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___114_5337.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___114_5337.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___114_5337.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___114_5337.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___114_5337.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___114_5337.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___114_5337.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___114_5337.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___114_5337.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___114_5337.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___114_5337.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___114_5337.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___114_5337.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___114_5337.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___114_5337.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___114_5337.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___114_5337.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___114_5337.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___114_5337.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5329 in
                           match uu____5325 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____5346 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5347 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5347) in
                                 if uu____5346
                                 then
                                   let uu____5348 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5348
                                 else
                                   (let guard2 =
                                      let uu____5351 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5351 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 let uu____5358 =
                                   let uu____5365 =
                                     let uu____5371 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     FStar_All.pipe_right uu____5371
                                       (fun _0_29  -> FStar_Util.Inl _0_29) in
                                   Some uu____5365 in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5358 in
                               let uu____5385 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5400 -> (e, t1, guard2)
                                      | uu____5408 ->
                                          let uu____5409 =
                                            if use_teq
                                            then
                                              let uu____5414 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5414)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5409 with
                                           | (e1,guard') ->
                                               let uu____5421 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5421)))
                                 | None  -> (e, tfun_computed, guard2) in
                               (match uu____5385 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____5434 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____5434 with
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
              (let uu____5470 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____5470
               then
                 let uu____5471 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____5472 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5471
                   uu____5472
               else ());
              (let monadic_application uu____5514 subst1 arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____5514 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___115_5555 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___115_5555.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___115_5555.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___115_5555.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____5556 =
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
                                     (fun uu___89_5583  ->
                                        match uu___89_5583 with
                                        | (uu____5592,uu____5593,FStar_Util.Inl
                                           uu____5594) -> false
                                        | (uu____5605,uu____5606,FStar_Util.Inr
                                           c) ->
                                            let uu____5616 =
                                              FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                c in
                                            Prims.op_Negation uu____5616))) in
                           let cres3 =
                             if refine_with_equality
                             then
                               let uu____5618 =
                                 (FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets))
                                   (Some
                                      ((cres2.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                   r in
                               FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                 env uu____5618 cres2
                             else
                               ((let uu____5629 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low in
                                 if uu____5629
                                 then
                                   let uu____5630 =
                                     FStar_Syntax_Print.term_to_string head2 in
                                   let uu____5631 =
                                     FStar_Syntax_Print.lcomp_to_string cres2 in
                                   let uu____5632 =
                                     FStar_TypeChecker_Rel.guard_to_string
                                       env g in
                                   FStar_Util.print3
                                     "Not refining result: f=%s; cres=%s; guard=%s\n"
                                     uu____5630 uu____5631 uu____5632
                                 else ());
                                cres2) in
                           (cres3, g)
                       | uu____5634 ->
                           let g =
                             let uu____5639 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____5639
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____5640 =
                             let uu____5641 =
                               let uu____5644 =
                                 let uu____5645 =
                                   let uu____5646 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____5646 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5645 in
                               FStar_Syntax_Syntax.mk_Total uu____5644 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5641 in
                           (uu____5640, g) in
                     (match uu____5556 with
                      | (cres2,guard1) ->
                          ((let uu____5657 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____5657
                            then
                              let uu____5658 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5658
                            else ());
                           (let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____5674  ->
                                     match uu____5674 with
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
                              let uu____5720 =
                                let uu____5721 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____5721.FStar_Syntax_Syntax.n in
                              match uu____5720 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____5725 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____5739  ->
                                         match uu____5739 with
                                         | (arg,uu____5751,uu____5752) -> arg
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
                                (let uu____5772 =
                                   let map_fun uu____5811 =
                                     match uu____5811 with
                                     | ((e,q),uu____5835,c0) ->
                                         (match c0 with
                                          | FStar_Util.Inl uu____5860 ->
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
                                              let uu____5903 =
                                                let uu____5906 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x in
                                                (uu____5906, q) in
                                              ((Some
                                                  (x,
                                                    (c.FStar_Syntax_Syntax.eff_name),
                                                    (c.FStar_Syntax_Syntax.res_typ),
                                                    e1)), uu____5903)) in
                                   let uu____5924 =
                                     let uu____5938 =
                                       let uu____5951 =
                                         let uu____5963 =
                                           let uu____5972 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____5972, None,
                                             (FStar_Util.Inr chead1)) in
                                         uu____5963 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____5951 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____5938 in
                                   match uu____5924 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6081 =
                                         let uu____6082 =
                                           FStar_List.hd reverse_args in
                                         Prims.fst uu____6082 in
                                       let uu____6087 =
                                         let uu____6091 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6091 in
                                       (lifted_args, uu____6081, uu____6087) in
                                 match uu____5772 with
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
                                     let bind_lifted_args e uu___90_6159 =
                                       match uu___90_6159 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6201 =
                                               let uu____6204 =
                                                 let uu____6205 =
                                                   let uu____6213 =
                                                     let uu____6214 =
                                                       let uu____6215 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6215] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6214 e in
                                                   ((false, [lb]),
                                                     uu____6213) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6205 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6204 in
                                             uu____6201 None
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
                            let uu____6249 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6249 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6307 bs args1 =
                 match uu____6307 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6402))::rest,
                         (uu____6404,None )::uu____6405) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 = check_no_escape (Some head1) env fvs t in
                          let uu____6442 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6442 with
                           | (varg,uu____6453,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6466 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6466) in
                               let uu____6467 =
                                 let uu____6489 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t1))) :: outargs), (arg ::
                                   arg_rets), uu____6489, fvs) in
                               tc_args head_info uu____6467 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____6580 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___116_6587 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___116_6587.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___116_6587.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6589 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6589
                             then
                               let uu____6590 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6590
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___117_6595 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___117_6595.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___117_6595.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___117_6595.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___117_6595.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___117_6595.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___117_6595.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___117_6595.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___117_6595.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___117_6595.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___117_6595.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___117_6595.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___117_6595.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___117_6595.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___117_6595.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___117_6595.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___117_6595.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___117_6595.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___117_6595.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___117_6595.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___117_6595.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___117_6595.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___117_6595.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___117_6595.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             (let uu____6597 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6597
                              then
                                let uu____6598 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6599 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6600 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6598 uu____6599 uu____6600
                              else ());
                             (let uu____6602 = tc_term env2 e in
                              match uu____6602 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let uu____6618 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
                                  if uu____6618
                                  then
                                    let subst2 =
                                      let uu____6623 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6623 e1 in
                                    tc_args head_info
                                      (subst2,
                                        ((arg, None,
                                           (FStar_Util.Inl
                                              ((c.FStar_Syntax_Syntax.eff_name),
                                                (c.FStar_Syntax_Syntax.res_typ))))
                                        :: outargs), (arg :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    (let uu____6679 =
                                       FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name in
                                     if uu____6679
                                     then
                                       let subst2 =
                                         let uu____6684 = FStar_List.hd bs in
                                         maybe_extend_subst subst1 uu____6684
                                           e1 in
                                       tc_args head_info
                                         (subst2,
                                           ((arg, (Some x1),
                                              (FStar_Util.Inr c)) ::
                                           outargs), (arg :: arg_rets), g1,
                                           fvs) rest rest'
                                     else
                                       (let uu____6730 =
                                          let uu____6731 = FStar_List.hd bs in
                                          FStar_Syntax_Syntax.is_null_binder
                                            uu____6731 in
                                        if uu____6730
                                        then
                                          let newx =
                                            FStar_Syntax_Syntax.new_bv
                                              (Some
                                                 (e1.FStar_Syntax_Syntax.pos))
                                              c.FStar_Syntax_Syntax.res_typ in
                                          let arg' =
                                            let uu____6740 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                newx in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____6740 in
                                          tc_args head_info
                                            (subst1,
                                              ((arg, (Some newx),
                                                 (FStar_Util.Inr c)) ::
                                              outargs), (arg' :: arg_rets),
                                              g1, fvs) rest rest'
                                        else
                                          (let uu____6778 =
                                             let uu____6800 =
                                               let uu____6802 =
                                                 let uu____6803 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x1 in
                                                 FStar_Syntax_Syntax.as_arg
                                                   uu____6803 in
                                               uu____6802 :: arg_rets in
                                             (subst1,
                                               ((arg, (Some x1),
                                                  (FStar_Util.Inr c)) ::
                                               outargs), uu____6800, g1, (x1
                                               :: fvs)) in
                                           tc_args head_info uu____6778 rest
                                             rest')))))))
                      | (uu____6840,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6861) ->
                          let uu____6891 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____6891 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6914 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____6914
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____6930 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____6930 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____6944 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____6944
                                            then
                                              let uu____6945 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____6945
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____6975 when Prims.op_Negation norm1 ->
                                     let uu____6976 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____6976
                                 | uu____6977 ->
                                     let uu____6978 =
                                       let uu____6979 =
                                         let uu____6982 =
                                           let uu____6983 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____6984 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6983 uu____6984 in
                                         let uu____6988 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____6982, uu____6988) in
                                       FStar_Errors.Error uu____6979 in
                                     Prims.raise uu____6978 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____7001 =
                   let uu____7002 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____7002.FStar_Syntax_Syntax.n in
                 match uu____7001 with
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
                           let uu____7078 = tc_term env1 e in
                           (match uu____7078 with
                            | (e1,c,g_e) ->
                                let uu____7091 = tc_args1 env1 tl1 in
                                (match uu____7091 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7113 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7113))) in
                     let uu____7124 = tc_args1 env args in
                     (match uu____7124 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7146 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7166  ->
                                      match uu____7166 with
                                      | (uu____7174,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7146 in
                          let ml_or_tot t r1 =
                            let uu____7190 = FStar_Options.ml_ish () in
                            if uu____7190
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7193 =
                              let uu____7196 =
                                let uu____7197 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7197 Prims.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7196 in
                            ml_or_tot uu____7193 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7206 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7206
                            then
                              let uu____7207 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7208 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7209 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7207 uu____7208 uu____7209
                            else ());
                           (let uu____7212 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7212);
                           (let comp =
                              let uu____7214 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7219  ->
                                   fun out  ->
                                     match uu____7219 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7214 in
                            let uu____7228 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7235 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7228, comp, uu____7235))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7250 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7250 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7294) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7300,uu____7301)
                     -> check_function_app t
                 | uu____7330 ->
                     let uu____7331 =
                       let uu____7332 =
                         let uu____7335 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7335, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7332 in
                     Prims.raise uu____7331 in
               check_function_app thead)
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
                  let uu____7386 =
                    FStar_List.fold_left2
                      (fun uu____7399  ->
                         fun uu____7400  ->
                           fun uu____7401  ->
                             match (uu____7399, uu____7400, uu____7401) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7445 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7445 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7457 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7457 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7459 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7459) &&
                                              (let uu____7460 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7460)) in
                                       let uu____7461 =
                                         let uu____7467 =
                                           let uu____7473 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7473] in
                                         FStar_List.append seen uu____7467 in
                                       let uu____7478 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7461, uu____7478, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7386 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____7507 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7507
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7509 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7509 with | (c2,g) -> (e, c2, g)))
              | uu____7521 ->
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
        let uu____7543 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7543 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7569 = branch1 in
            (match uu____7569 with
             | (cpat,uu____7589,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7631 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0 in
                   match uu____7631 with
                   | (pat_bvs1,exps,p) ->
                       ((let uu____7653 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____7653
                         then
                           let uu____7654 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____7655 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7654 uu____7655
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____7658 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____7658 with
                         | (env1,uu____7671) ->
                             let env11 =
                               let uu___118_7675 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___118_7675.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___118_7675.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___118_7675.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___118_7675.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___118_7675.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___118_7675.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___118_7675.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___118_7675.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___118_7675.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___118_7675.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___118_7675.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___118_7675.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___118_7675.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___118_7675.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___118_7675.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___118_7675.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___118_7675.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___118_7675.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___118_7675.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___118_7675.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___118_7675.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___118_7675.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___118_7675.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             let uu____7677 =
                               let uu____7682 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____7694 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High in
                                          if uu____7694
                                          then
                                            let uu____7695 =
                                              FStar_Syntax_Print.term_to_string
                                                e in
                                            let uu____7696 =
                                              FStar_Syntax_Print.term_to_string
                                                pat_t in
                                            FStar_Util.print2
                                              "Checking pattern expression %s against expected type %s\n"
                                              uu____7695 uu____7696
                                          else ());
                                         (let uu____7698 = tc_term env11 e in
                                          match uu____7698 with
                                          | (e1,lc,g) ->
                                              ((let uu____7708 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High in
                                                if uu____7708
                                                then
                                                  let uu____7709 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env e1 in
                                                  let uu____7710 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  FStar_Util.print2
                                                    "Pre-checked pattern expression %s at type %s\n"
                                                    uu____7709 uu____7710
                                                else ());
                                               (let g' =
                                                  FStar_TypeChecker_Rel.teq
                                                    env
                                                    lc.FStar_Syntax_Syntax.res_typ
                                                    expected_pat_t in
                                                let g1 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g' in
                                                let uu____7714 =
                                                  let uu____7715 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___119_7716 = g1 in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___119_7716.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___119_7716.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___119_7716.FStar_TypeChecker_Env.implicits)
                                                       }) in
                                                  FStar_All.pipe_right
                                                    uu____7715
                                                    FStar_TypeChecker_Rel.resolve_implicits in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e1 in
                                                let uvars_to_string uvs =
                                                  let uu____7730 =
                                                    let uu____7732 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements in
                                                    FStar_All.pipe_right
                                                      uu____7732
                                                      (FStar_List.map
                                                         (fun uu____7756  ->
                                                            match uu____7756
                                                            with
                                                            | (u,uu____7761)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u)) in
                                                  FStar_All.pipe_right
                                                    uu____7730
                                                    (FStar_String.concat ", ") in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e' in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t in
                                                (let uu____7774 =
                                                   let uu____7775 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2 in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation
                                                     uu____7775 in
                                                 if uu____7774
                                                 then
                                                   let unresolved =
                                                     let uu____7782 =
                                                       FStar_Util.set_difference
                                                         uvs1 uvs2 in
                                                     FStar_All.pipe_right
                                                       uu____7782
                                                       FStar_Util.set_elements in
                                                   let uu____7796 =
                                                     let uu____7797 =
                                                       let uu____7800 =
                                                         let uu____7801 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env e' in
                                                         let uu____7802 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env
                                                             expected_pat_t in
                                                         let uu____7803 =
                                                           let uu____7804 =
                                                             FStar_All.pipe_right
                                                               unresolved
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____7816
                                                                     ->
                                                                    match uu____7816
                                                                    with
                                                                    | 
                                                                    (u,uu____7824)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u)) in
                                                           FStar_All.pipe_right
                                                             uu____7804
                                                             (FStar_String.concat
                                                                ", ") in
                                                         FStar_Util.format3
                                                           "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                           uu____7801
                                                           uu____7802
                                                           uu____7803 in
                                                       (uu____7800,
                                                         (p.FStar_Syntax_Syntax.p)) in
                                                     FStar_Errors.Error
                                                       uu____7797 in
                                                   Prims.raise uu____7796
                                                 else ());
                                                (let uu____7839 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High in
                                                 if uu____7839
                                                 then
                                                   let uu____7840 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env e1 in
                                                   FStar_Util.print1
                                                     "Done checking pattern expression %s\n"
                                                     uu____7840
                                                 else ());
                                                (e1, e')))))) in
                               FStar_All.pipe_right uu____7682
                                 FStar_List.unzip in
                             (match uu____7677 with
                              | (exps1,norm_exps) ->
                                  let p1 =
                                    FStar_TypeChecker_Util.decorate_pattern
                                      env p exps1 in
                                  (p1, pat_bvs1, pat_env, exps1, norm_exps)))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____7871 =
                   let uu____7875 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____7875
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____7871 with
                  | (scrutinee_env,uu____7888) ->
                      let uu____7891 = tc_pat true pat_t pattern in
                      (match uu____7891 with
                       | (pattern1,pat_bvs1,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____7919 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____7934 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____7934
                                 then
                                   Prims.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____7942 =
                                      let uu____7946 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____7946 e in
                                    match uu____7942 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____7919 with
                            | (when_clause1,g_when) ->
                                let uu____7966 = tc_term pat_env branch_exp in
                                (match uu____7966 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____7985 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_30  -> Some _0_30)
                                             uu____7985 in
                                     let uu____7987 =
                                       let eqs =
                                         let uu____7993 =
                                           let uu____7994 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____7994 in
                                         if uu____7993
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
                                                     | uu____8008 ->
                                                         let clause =
                                                           let uu____8010 =
                                                             env.FStar_TypeChecker_Env.universe_of
                                                               env pat_t in
                                                           FStar_Syntax_Util.mk_eq2
                                                             uu____8010 pat_t
                                                             scrutinee_tm e1 in
                                                         (match fopt with
                                                          | None  ->
                                                              Some clause
                                                          | Some f ->
                                                              let uu____8013
                                                                =
                                                                FStar_Syntax_Util.mk_disj
                                                                  clause f in
                                                              FStar_All.pipe_left
                                                                (fun _0_31 
                                                                   ->
                                                                   Some _0_31)
                                                                uu____8013))
                                                None) in
                                       let uu____8023 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____8023 with
                                       | (c1,g_branch1) ->
                                           let uu____8033 =
                                             match (eqs, when_condition) with
                                             | uu____8040 when
                                                 let uu____8045 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8045
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____8053 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8054 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8053, uu____8054)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____8061 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8061 in
                                                 let uu____8062 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8063 =
                                                   let uu____8064 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8064 g_when in
                                                 (uu____8062, uu____8063)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____8070 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8070, g_when) in
                                           (match uu____8033 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____8078 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs1 c_weak in
                                                let uu____8079 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8078, uu____8079,
                                                  g_branch1)) in
                                     (match uu____7987 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8092 =
                                              let uu____8093 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8093 in
                                            if uu____8092
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8124 =
                                                     let uu____8125 =
                                                       let uu____8126 =
                                                         let uu____8128 =
                                                           let uu____8132 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8132 in
                                                         Prims.snd uu____8128 in
                                                       FStar_List.length
                                                         uu____8126 in
                                                     uu____8125 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8124
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____8141 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8141 with
                                                     | None  -> []
                                                     | uu____8152 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None in
                                                         let disc1 =
                                                           let uu____8162 =
                                                             let uu____8163 =
                                                               let uu____8164
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8164] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8163 in
                                                           uu____8162 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8169 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool in
                                                         [uu____8169]
                                                   else [] in
                                                 let fail uu____8177 =
                                                   let uu____8178 =
                                                     let uu____8179 =
                                                       FStar_Range.string_of_range
                                                         pat_exp.FStar_Syntax_Syntax.pos in
                                                     let uu____8180 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp in
                                                     let uu____8181 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8179 uu____8180
                                                       uu____8181 in
                                                   failwith uu____8178 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8202) ->
                                                       head_constructor t1
                                                   | uu____8208 -> fail () in
                                                 let pat_exp1 =
                                                   let uu____8211 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp in
                                                   FStar_All.pipe_right
                                                     uu____8211
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
                                                     let uu____8228 =
                                                       let uu____8229 =
                                                         tc_constant
                                                           pat_exp1.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8229
                                                         scrutinee_tm1
                                                         pat_exp1 in
                                                     [uu____8228]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                   _
                                                   |FStar_Syntax_Syntax.Tm_fvar
                                                   _ ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp1 in
                                                     let uu____8237 =
                                                       let uu____8238 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8238 in
                                                     if uu____8237
                                                     then []
                                                     else
                                                       (let uu____8245 =
                                                          head_constructor
                                                            pat_exp1 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8245)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8272 =
                                                       let uu____8273 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8273 in
                                                     if uu____8272
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8282 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8298
                                                                     ->
                                                                    match uu____8298
                                                                    with
                                                                    | 
                                                                    (ei,uu____8305)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8315
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8315
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8326
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8335
                                                                    =
                                                                    let uu____8336
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None in
                                                                    let uu____8341
                                                                    =
                                                                    let uu____8342
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8342] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8336
                                                                    uu____8341 in
                                                                    uu____8335
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8282
                                                            FStar_List.flatten in
                                                        let uu____8354 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8354
                                                          sub_term_guards)
                                                 | uu____8358 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8370 =
                                                   let uu____8371 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8371 in
                                                 if uu____8370
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8374 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8374 in
                                                    let uu____8377 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8377 with
                                                    | (k,uu____8381) ->
                                                        let uu____8382 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8382
                                                         with
                                                         | (t1,uu____8387,uu____8388)
                                                             -> t1)) in
                                               let branch_guard =
                                                 let uu____8390 =
                                                   FStar_All.pipe_right
                                                     norm_disj_exps
                                                     (FStar_List.map
                                                        (build_and_check_branch_guard
                                                           scrutinee_tm)) in
                                                 FStar_All.pipe_right
                                                   uu____8390
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
                                          ((let uu____8401 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8401
                                            then
                                              let uu____8402 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8402
                                            else ());
                                           (let uu____8404 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8404, branch_guard, c1,
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
          let uu____8422 = check_let_bound_def true env1 lb in
          (match uu____8422 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8436 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then (g1, e1, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8447 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8447
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8449 =
                      let uu____8454 =
                        let uu____8460 =
                          let uu____8465 =
                            let uu____8473 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8473) in
                          [uu____8465] in
                        FStar_TypeChecker_Util.generalize env1 uu____8460 in
                      FStar_List.hd uu____8454 in
                    match uu____8449 with
                    | (uu____8502,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8436 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8513 =
                      let uu____8518 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8518
                      then
                        let uu____8523 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8523 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8540 =
                                   FStar_Options.warn_top_level_effects () in
                                 if uu____8540
                                 then
                                   let uu____8541 =
                                     FStar_TypeChecker_Env.get_range env1 in
                                   FStar_Errors.warn uu____8541
                                     FStar_TypeChecker_Err.top_level_effect
                                 else ());
                                (let uu____8543 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos in
                                 (uu____8543, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8561 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8561
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8569 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8569
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____8513 with
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
                           let uu____8601 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8601,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8620 -> failwith "Impossible"
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
            let uu___120_8641 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___120_8641.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___120_8641.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___120_8641.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___120_8641.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___120_8641.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___120_8641.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___120_8641.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___120_8641.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___120_8641.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___120_8641.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___120_8641.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___120_8641.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___120_8641.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___120_8641.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___120_8641.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___120_8641.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___120_8641.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___120_8641.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___120_8641.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___120_8641.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___120_8641.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___120_8641.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___120_8641.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____8642 =
            let uu____8648 =
              let uu____8649 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8649 Prims.fst in
            check_let_bound_def false uu____8648 lb in
          (match uu____8642 with
           | (e1,uu____8661,c1,g1,annotated) ->
               let x =
                 let uu___121_8666 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___121_8666.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___121_8666.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8667 =
                 let uu____8670 =
                   let uu____8671 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8671] in
                 FStar_Syntax_Subst.open_term uu____8670 e2 in
               (match uu____8667 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = Prims.fst xbinder in
                    let uu____8683 =
                      let uu____8687 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8687 e21 in
                    (match uu____8683 with
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
                           let uu____8702 =
                             let uu____8705 =
                               let uu____8706 =
                                 let uu____8714 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8714) in
                               FStar_Syntax_Syntax.Tm_let uu____8706 in
                             FStar_Syntax_Syntax.mk uu____8705 in
                           uu____8702
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____8729 =
                             let uu____8730 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____8731 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____8730
                               c1.FStar_Syntax_Syntax.res_typ uu____8731 e11 in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8729 in
                         let g21 =
                           let uu____8733 =
                             let uu____8734 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____8734 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____8733 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____8736 =
                           let uu____8737 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____8737 in
                         if uu____8736
                         then
                           let tt =
                             let uu____8743 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____8743 FStar_Option.get in
                           ((let uu____8747 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8747
                             then
                               let uu____8748 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____8749 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____8748 uu____8749
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____8754 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8754
                             then
                               let uu____8755 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____8756 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8755 uu____8756
                             else ());
                            (e4,
                              ((let uu___122_8758 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___122_8758.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___122_8758.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___122_8758.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8759 -> failwith "Impossible"
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
          let uu____8780 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8780 with
           | (lbs1,e21) ->
               let uu____8791 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8791 with
                | (env0,topt) ->
                    let uu____8802 = build_let_rec_env true env0 lbs1 in
                    (match uu____8802 with
                     | (lbs2,rec_env) ->
                         let uu____8813 = check_let_recs rec_env lbs2 in
                         (match uu____8813 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8825 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____8825
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____8829 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____8829
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
                                     let uu____8853 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____8875 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____8875))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8853 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____8895  ->
                                           match uu____8895 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____8920 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____8920 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____8929 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____8929 with
                                | (lbs5,e22) ->
                                    let uu____8940 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____8955 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env1 g_lbs1 in
                                    (uu____8940, cres, uu____8955)))))))
      | uu____8958 -> failwith "Impossible"
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
          let uu____8979 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8979 with
           | (lbs1,e21) ->
               let uu____8990 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8990 with
                | (env0,topt) ->
                    let uu____9001 = build_let_rec_env false env0 lbs1 in
                    (match uu____9001 with
                     | (lbs2,rec_env) ->
                         let uu____9012 = check_let_recs rec_env lbs2 in
                         (match uu____9012 with
                          | (lbs3,g_lbs) ->
                              let uu____9023 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___123_9034 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___123_9034.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___123_9034.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___124_9036 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___124_9036.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___124_9036.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___124_9036.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___124_9036.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____9023 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____9053 = tc_term env2 e21 in
                                   (match uu____9053 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9064 =
                                            let uu____9065 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9065 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9064 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_comp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___125_9069 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___125_9069.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___125_9069.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___125_9069.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9070 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9070 with
                                         | (lbs5,e23) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | Some uu____9099 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres in
                                                  let cres3 =
                                                    let uu___126_9104 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___126_9104.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___126_9104.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___126_9104.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9107 -> failwith "Impossible"
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
          let uu____9123 = FStar_Syntax_Util.arrow_formals_comp t in
          match uu____9123 with
          | (uu____9129,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c) in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect) in
        let uu____9140 =
          FStar_List.fold_left
            (fun uu____9147  ->
               fun lb  ->
                 match uu____9147 with
                 | (lbs1,env1) ->
                     let uu____9159 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9159 with
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
                              (let uu____9173 =
                                 let uu____9177 =
                                   let uu____9178 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left Prims.fst uu____9178 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___127_9183 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___127_9183.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___127_9183.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___127_9183.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___127_9183.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___127_9183.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___127_9183.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___127_9183.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___127_9183.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___127_9183.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___127_9183.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___127_9183.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___127_9183.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___127_9183.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___127_9183.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___127_9183.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___127_9183.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___127_9183.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___127_9183.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___127_9183.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___127_9183.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___127_9183.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___127_9183.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___127_9183.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____9177 in
                               match uu____9173 with
                               | (t1,uu____9185,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9189 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left Prims.ignore
                                       uu____9189);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9191 =
                              (termination_check_enabled t1) &&
                                (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9191
                            then
                              let uu___128_9192 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___128_9192.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___128_9192.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___128_9192.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___128_9192.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___128_9192.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___128_9192.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___128_9192.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___128_9192.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___128_9192.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___128_9192.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___128_9192.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___128_9192.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___128_9192.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___128_9192.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___128_9192.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___128_9192.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___128_9192.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___128_9192.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___128_9192.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___128_9192.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___128_9192.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___128_9192.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___128_9192.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___129_9202 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___129_9202.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___129_9202.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9140 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9216 =
        let uu____9221 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____9232 =
                    let uu____9236 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp in
                    tc_tot_or_gtot_term uu____9236
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____9232 with
                  | (e,c,g) ->
                      ((let uu____9243 =
                          let uu____9244 = FStar_Syntax_Util.is_total_lcomp c in
                          Prims.op_Negation uu____9244 in
                        if uu____9243
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
        FStar_All.pipe_right uu____9221 FStar_List.unzip in
      match uu____9216 with
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
        let uu____9273 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9273 with
        | (env1,uu____9283) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9289 = check_lbtyp top_level env lb in
            (match uu____9289 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9315 =
                     tc_maybe_toplevel_term
                       (let uu___130_9319 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___130_9319.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___130_9319.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___130_9319.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___130_9319.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___130_9319.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___130_9319.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___130_9319.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___130_9319.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___130_9319.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___130_9319.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___130_9319.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___130_9319.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___130_9319.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___130_9319.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___130_9319.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___130_9319.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___130_9319.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___130_9319.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___130_9319.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___130_9319.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___130_9319.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___130_9319.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___130_9319.FStar_TypeChecker_Env.qname_and_index)
                        }) e11 in
                   match uu____9315 with
                   | (e12,c1,g1) ->
                       let uu____9328 =
                         let uu____9331 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9334  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9331 e12 c1 wf_annot in
                       (match uu____9328 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9344 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9344
                              then
                                let uu____9345 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9346 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9347 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9345 uu____9346 uu____9347
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
        | uu____9373 ->
            let uu____9374 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9374 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9401 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9401)
                 else
                   (let uu____9406 = FStar_Syntax_Util.type_u () in
                    match uu____9406 with
                    | (k,uu____9417) ->
                        let uu____9418 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9418 with
                         | (t2,uu____9430,g) ->
                             ((let uu____9433 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9433
                               then
                                 let uu____9434 =
                                   let uu____9435 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9435 in
                                 let uu____9436 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9434 uu____9436
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9439 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9439))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9444  ->
      match uu____9444 with
      | (x,imp) ->
          let uu____9455 = FStar_Syntax_Util.type_u () in
          (match uu____9455 with
           | (tu,u) ->
               ((let uu____9467 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9467
                 then
                   let uu____9468 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9469 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9470 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9468 uu____9469 uu____9470
                 else ());
                (let uu____9472 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9472 with
                 | (t,uu____9483,g) ->
                     let x1 =
                       ((let uu___131_9488 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___131_9488.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___131_9488.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9490 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9490
                       then
                         let uu____9491 =
                           FStar_Syntax_Print.bv_to_string (Prims.fst x1) in
                         let uu____9492 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9491 uu____9492
                       else ());
                      (let uu____9494 = push_binding env x1 in
                       (x1, uu____9494, g, u))))))
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
            let uu____9545 = tc_binder env1 b in
            (match uu____9545 with
             | (b1,env',g,u) ->
                 let uu____9568 = aux env' bs2 in
                 (match uu____9568 with
                  | (bs3,env'1,g',us) ->
                      let uu____9597 =
                        let uu____9598 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____9598 in
                      ((b1 :: bs3), env'1, uu____9597, (u :: us)))) in
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
          (fun uu____9641  ->
             fun uu____9642  ->
               match (uu____9641, uu____9642) with
               | ((t,imp),(args1,g)) ->
                   let uu____9679 = tc_term env1 t in
                   (match uu____9679 with
                    | (t1,uu____9689,g') ->
                        let uu____9691 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____9691))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9709  ->
             match uu____9709 with
             | (pats1,g) ->
                 let uu____9723 = tc_args env p in
                 (match uu____9723 with
                  | (args,g') ->
                      let uu____9731 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____9731))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____9739 = tc_maybe_toplevel_term env e in
      match uu____9739 with
      | (e1,c,g) ->
          let uu____9749 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____9749
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____9759 =
               let uu____9762 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____9762
               then
                 let uu____9765 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____9765, false)
               else
                 (let uu____9767 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____9767, true)) in
             match uu____9759 with
             | (target_comp,allow_ghost) ->
                 let uu____9773 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____9773 with
                  | Some g' ->
                      let uu____9779 = FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____9779)
                  | uu____9780 ->
                      if allow_ghost
                      then
                        let uu____9785 =
                          let uu____9786 =
                            let uu____9789 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____9789, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____9786 in
                        Prims.raise uu____9785
                      else
                        (let uu____9794 =
                           let uu____9795 =
                             let uu____9798 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____9798, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____9795 in
                         Prims.raise uu____9794)))
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
      let uu____9811 = tc_tot_or_gtot_term env t in
      match uu____9811 with
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
      (let uu____9831 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9831
       then
         let uu____9832 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____9832
       else ());
      (let env1 =
         let uu___132_9835 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___132_9835.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___132_9835.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___132_9835.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___132_9835.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___132_9835.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___132_9835.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___132_9835.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___132_9835.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___132_9835.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___132_9835.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___132_9835.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___132_9835.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___132_9835.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___132_9835.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___132_9835.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___132_9835.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___132_9835.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___132_9835.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___132_9835.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___132_9835.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___132_9835.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____9838 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____9854) ->
             let uu____9855 =
               let uu____9856 =
                 let uu____9859 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____9859) in
               FStar_Errors.Error uu____9856 in
             Prims.raise uu____9855 in
       match uu____9838 with
       | (t,c,g) ->
           let uu____9869 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____9869
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____9876 =
                let uu____9877 =
                  let uu____9880 =
                    let uu____9881 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____9881 in
                  let uu____9882 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____9880, uu____9882) in
                FStar_Errors.Error uu____9877 in
              Prims.raise uu____9876))
let level_of_type_fail env e t =
  let uu____9903 =
    let uu____9904 =
      let uu____9907 =
        let uu____9908 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____9908 t in
      let uu____9909 = FStar_TypeChecker_Env.get_range env in
      (uu____9907, uu____9909) in
    FStar_Errors.Error uu____9904 in
  Prims.raise uu____9903
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____9926 =
            let uu____9927 = FStar_Syntax_Util.unrefine t1 in
            uu____9927.FStar_Syntax_Syntax.n in
          match uu____9926 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____9931 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____9934 = FStar_Syntax_Util.type_u () in
                 match uu____9934 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___135_9940 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___135_9940.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___135_9940.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___135_9940.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___135_9940.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___135_9940.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___135_9940.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___135_9940.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___135_9940.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___135_9940.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___135_9940.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___135_9940.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___135_9940.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___135_9940.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___135_9940.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___135_9940.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___135_9940.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___135_9940.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___135_9940.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___135_9940.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___135_9940.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___135_9940.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___135_9940.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___135_9940.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____9944 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____9944
                       | uu____9945 ->
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
      let uu____9954 =
        let uu____9955 = FStar_Syntax_Subst.compress e in
        uu____9955.FStar_Syntax_Syntax.n in
      match uu____9954 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____9964 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____9975) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10000,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10015) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10022 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10022 with | ((uu____10033,t),uu____10035) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10038,(FStar_Util.Inl t,uu____10040),uu____10041) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10077,(FStar_Util.Inr c,uu____10079),uu____10080) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10127;
             FStar_Syntax_Syntax.pos = uu____10128;
             FStar_Syntax_Syntax.vars = uu____10129;_},us)
          ->
          let uu____10135 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10135 with
           | ((us',t),uu____10148) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10156 =
                     let uu____10157 =
                       let uu____10160 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10160) in
                     FStar_Errors.Error uu____10157 in
                   Prims.raise uu____10156)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____10168 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10169 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10177) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10194 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10194 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10205  ->
                      match uu____10205 with
                      | (b,uu____10209) ->
                          let uu____10210 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10210) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10215 = universe_of_aux env res in
                 level_of_type env res uu____10215 in
               let u_c =
                 let uu____10217 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10217 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10220 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10220 in
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
                let uu____10306 = universe_of_aux env hd3 in
                (uu____10306, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10316,hd4::uu____10318) ->
                let uu____10365 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____10365 with
                 | (uu____10375,uu____10376,hd5) ->
                     let uu____10392 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____10392 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10427 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____10429 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____10429 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10464 ->
                let uu____10465 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____10465 with
                 | (env1,uu____10479) ->
                     let env2 =
                       let uu___136_10483 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___136_10483.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___136_10483.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___136_10483.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___136_10483.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___136_10483.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___136_10483.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___136_10483.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___136_10483.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___136_10483.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___136_10483.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___136_10483.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___136_10483.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___136_10483.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___136_10483.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___136_10483.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___136_10483.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___136_10483.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___136_10483.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___136_10483.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___136_10483.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___136_10483.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     ((let uu____10485 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____10485
                       then
                         let uu____10486 =
                           let uu____10487 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____10487 in
                         let uu____10488 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10486 uu____10488
                       else ());
                      (let uu____10490 = tc_term env2 hd3 in
                       match uu____10490 with
                       | (uu____10503,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10504;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10506;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10507;_},g)
                           ->
                           ((let uu____10517 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____10517 Prims.ignore);
                            (t, args1))))) in
          let uu____10525 = type_of_head true hd1 args in
          (match uu____10525 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____10554 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____10554 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____10587 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____10587)))
      | FStar_Syntax_Syntax.Tm_match (uu____10590,hd1::uu____10592) ->
          let uu____10639 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____10639 with
           | (uu____10642,uu____10643,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____10659,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____10693 = universe_of_aux env e in
      level_of_type env e uu____10693
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____10706 = tc_binders env tps in
      match uu____10706 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))