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
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
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
          (FStar_Util.Inl
             (fun uu____186  ->
                let uu____187 =
                  let uu____190 = FStar_Syntax_Syntax.get_lazy_comp lc in
                  uu____190 () in
                FStar_Syntax_Util.set_result_typ uu____187 t))
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
            let uu____229 =
              let uu____230 = FStar_Syntax_Subst.compress t in
              uu____230.FStar_Syntax_Syntax.n in
            match uu____229 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____233,c) ->
                let uu____245 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____245
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____247 =
                    let uu____248 = FStar_Syntax_Subst.compress t1 in
                    uu____248.FStar_Syntax_Syntax.n in
                  (match uu____247 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____252 -> false
                   | uu____253 -> true)
                else false
            | uu____255 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____258 =
                  let uu____261 =
                    (let uu____262 = should_return t in
                     Prims.op_Negation uu____262) ||
                      (let uu____263 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____263) in
                  if uu____261
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____258
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____271 =
            let uu____275 = FStar_TypeChecker_Env.expected_typ env in
            match uu____275 with
            | None  -> let uu____280 = memo_tk e t in (uu____280, lc, guard)
            | Some t' ->
                ((let uu____283 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____283
                  then
                    let uu____284 = FStar_Syntax_Print.term_to_string t in
                    let uu____285 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____284
                      uu____285
                  else ());
                 (let uu____287 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____287 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____298 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____298 with
                       | (e2,g) ->
                           ((let uu____307 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____307
                             then
                               let uu____308 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____309 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____310 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____311 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____308 uu____309 uu____310 uu____311
                             else ());
                            (let msg =
                               let uu____317 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____317
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_28  -> Some _0_28)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____332 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____332 with
                             | (lc2,g2) ->
                                 let uu____340 = memo_tk e2 t' in
                                 (uu____340, (set_lcomp_result lc2 t'), g2)))))) in
          match uu____271 with
          | (e1,lc1,g) ->
              ((let uu____348 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____348
                then
                  let uu____349 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____349
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
        let uu____366 = FStar_TypeChecker_Env.expected_typ env in
        match uu____366 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____372 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____372 with
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
      fun uu____394  ->
        match uu____394 with
        | (e,c) ->
            let expected_c_opt =
              match copt with
              | Some uu____409 -> copt
              | None  ->
                  let uu____410 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Syntax_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____411 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____411)) in
                  if uu____410
                  then
                    let uu____413 =
                      FStar_Syntax_Util.ml_comp
                        (FStar_Syntax_Util.comp_result c)
                        e.FStar_Syntax_Syntax.pos in
                    Some uu____413
                  else
                    (let uu____415 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____415
                     then None
                     else
                       (let uu____418 = FStar_Syntax_Util.is_pure_comp c in
                        if uu____418
                        then
                          let uu____420 =
                            FStar_Syntax_Syntax.mk_Total
                              (FStar_Syntax_Util.comp_result c) in
                          Some uu____420
                        else
                          (let uu____422 =
                             FStar_Syntax_Util.is_pure_or_ghost_comp c in
                           if uu____422
                           then
                             let uu____424 =
                               FStar_Syntax_Syntax.mk_GTotal
                                 (FStar_Syntax_Util.comp_result c) in
                             Some uu____424
                           else None))) in
            (match expected_c_opt with
             | None  ->
                 let uu____429 = norm_c env c in
                 (e, uu____429, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____432 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low in
                   if uu____432
                   then
                     let uu____433 = FStar_Syntax_Print.term_to_string e in
                     let uu____434 = FStar_Syntax_Print.comp_to_string c in
                     let uu____435 =
                       FStar_Syntax_Print.comp_to_string expected_c in
                     FStar_Util.print3
                       "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                       uu____433 uu____434 uu____435
                   else ());
                  (let c1 = norm_c env c in
                   (let uu____439 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low in
                    if uu____439
                    then
                      let uu____440 = FStar_Syntax_Print.term_to_string e in
                      let uu____441 = FStar_Syntax_Print.comp_to_string c1 in
                      let uu____442 =
                        FStar_Syntax_Print.comp_to_string expected_c in
                      FStar_Util.print3
                        "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                        uu____440 uu____441 uu____442
                    else ());
                   (let uu____444 =
                      FStar_TypeChecker_Util.check_comp env e c1 expected_c in
                    match uu____444 with
                    | (e1,uu____452,g) ->
                        let g1 =
                          let uu____455 = FStar_TypeChecker_Env.get_range env in
                          FStar_TypeChecker_Util.label_guard uu____455
                            "could not prove post-condition" g in
                        ((let uu____457 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low in
                          if uu____457
                          then
                            let uu____458 =
                              FStar_Range.string_of_range
                                e1.FStar_Syntax_Syntax.pos in
                            let uu____459 =
                              FStar_TypeChecker_Rel.guard_to_string env g1 in
                            FStar_Util.print2
                              "(%s) DONE check_expected_effect; guard is: %s\n"
                              uu____458 uu____459
                          else ());
                         (let e2 =
                            FStar_TypeChecker_Util.maybe_lift env e1
                              (FStar_Syntax_Util.comp_effect_name c1)
                              (FStar_Syntax_Util.comp_effect_name expected_c)
                              (FStar_Syntax_Util.comp_result c1) in
                          (e2, expected_c, g1)))))))
let no_logical_guard env uu____481 =
  match uu____481 with
  | (te,kt,f) ->
      let uu____488 = FStar_TypeChecker_Rel.guard_form f in
      (match uu____488 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____493 =
             let uu____494 =
               let uu____497 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____498 = FStar_TypeChecker_Env.get_range env in
               (uu____497, uu____498) in
             FStar_Errors.Error uu____494 in
           Prims.raise uu____493)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____505 = FStar_TypeChecker_Env.expected_typ env in
    match uu____505 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____508 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____508
let check_smt_pat env t bs c =
  let uu____543 = FStar_Syntax_Util.is_smt_lemma t in
  if uu____543
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____544;
          FStar_Syntax_Syntax.effect_name = uu____545;
          FStar_Syntax_Syntax.result_typ = uu____546;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____550)::[];
          FStar_Syntax_Syntax.flags = uu____551;_}
        ->
        let pat_vars =
          let uu____585 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats in
          FStar_Syntax_Free.names uu____585 in
        let uu____586 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____598  ->
                  match uu____598 with
                  | (b,uu____602) ->
                      let uu____603 = FStar_Util.set_mem b pat_vars in
                      Prims.op_Negation uu____603)) in
        (match uu____586 with
         | None  -> ()
         | Some (x,uu____607) ->
             let uu____610 =
               let uu____611 = FStar_Syntax_Print.bv_to_string x in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____611 in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____610)
    | uu____612 -> failwith "Impossible"
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
        let uu____633 =
          let uu____634 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____634 in
        if uu____633
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___89_652 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___89_652.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___89_652.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___89_652.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___89_652.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___89_652.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___89_652.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___89_652.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___89_652.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___89_652.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___89_652.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___89_652.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___89_652.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___89_652.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___89_652.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___89_652.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___89_652.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___89_652.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___89_652.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___89_652.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___89_652.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___89_652.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___89_652.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___89_652.FStar_TypeChecker_Env.qname_and_index)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____675  ->
                           match uu____675 with
                           | (b,uu____680) ->
                               let t =
                                 let uu____682 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 unfold_whnf env1 uu____682 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type _
                                  |FStar_Syntax_Syntax.Tm_arrow _ -> []
                                | uu____686 ->
                                    let uu____687 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____687]))) in
                 let as_lex_list dec =
                   let uu____692 = FStar_Syntax_Util.head_and_args dec in
                   match uu____692 with
                   | (head1,uu____703) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____719 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____722 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___81_726  ->
                           match uu___81_726 with
                           | FStar_Syntax_Syntax.DECREASES uu____727 -> true
                           | uu____730 -> false)) in
                 match uu____722 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____734 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____740 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____752 =
                 match uu____752 with
                 | (l,t) ->
                     let uu____761 =
                       let uu____762 = FStar_Syntax_Subst.compress t in
                       uu____762.FStar_Syntax_Syntax.n in
                     (match uu____761 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____795  ->
                                    match uu____795 with
                                    | (x,imp) ->
                                        let uu____802 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____802
                                        then
                                          let uu____805 =
                                            let uu____806 =
                                              let uu____808 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              Some uu____808 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____806
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____805, imp)
                                        else (x, imp))) in
                          let uu____810 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____810 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____823 =
                                   let uu____824 =
                                     let uu____825 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____826 =
                                       let uu____828 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____828] in
                                     uu____825 :: uu____826 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____824 in
                                 uu____823 None r in
                               let uu____833 = FStar_Util.prefix formals2 in
                               (match uu____833 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___90_859 = last1 in
                                      let uu____860 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___90_859.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___90_859.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____860
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____877 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____877
                                      then
                                        let uu____878 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____879 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____880 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____878 uu____879 uu____880
                                      else ());
                                     (l, t'))))
                      | uu____884 ->
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
        (let uu___91_1156 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___91_1156.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___91_1156.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___91_1156.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___91_1156.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___91_1156.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___91_1156.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___91_1156.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___91_1156.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___91_1156.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___91_1156.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___91_1156.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___91_1156.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___91_1156.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___91_1156.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___91_1156.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___91_1156.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___91_1156.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___91_1156.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___91_1156.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___91_1156.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___91_1156.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___91_1156.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___91_1156.FStar_TypeChecker_Env.qname_and_index)
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
      (let uu____1165 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1165
       then
         let uu____1166 =
           let uu____1167 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1167 in
         let uu____1168 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1166 uu____1168
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1174 -> failwith "Impossible"
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
           let uu____1213 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1213 with
            | (e2,c,g) ->
                let g1 =
                  let uu___92_1224 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___92_1224.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___92_1224.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___92_1224.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1237 = FStar_Syntax_Util.type_u () in
           (match uu____1237 with
            | (t,u) ->
                let uu____1245 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1245 with
                 | (e2,c,g) ->
                     let uu____1255 =
                       let uu____1264 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1264 with
                       | (env2,uu____1277) -> tc_pats env2 pats in
                     (match uu____1255 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___93_1298 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___93_1298.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___93_1298.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___93_1298.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1299 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1310 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1299, c, uu____1310))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1318 =
             let uu____1319 = FStar_Syntax_Subst.compress e1 in
             uu____1319.FStar_Syntax_Syntax.n in
           (match uu____1318 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1325,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1327;
                               FStar_Syntax_Syntax.lbtyp = uu____1328;
                               FStar_Syntax_Syntax.lbeff = uu____1329;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1347 =
                  let uu____1351 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1351 e11 in
                (match uu____1347 with
                 | (e12,c1,g1) ->
                     let uu____1358 = tc_term env1 e2 in
                     (match uu____1358 with
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
                            let uu____1375 =
                              let uu____1378 =
                                let uu____1379 =
                                  let uu____1387 =
                                    let uu____1391 =
                                      let uu____1393 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1393] in
                                    (false, uu____1391) in
                                  (uu____1387, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1379 in
                              FStar_Syntax_Syntax.mk uu____1378 in
                            uu____1375
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
                          let uu____1423 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1423)))
            | uu____1426 ->
                let uu____1427 = tc_term env1 e1 in
                (match uu____1427 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1451) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1466 = tc_term env1 e1 in
           (match uu____1466 with
            | (e2,c,g) ->
                let e3 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1492) ->
           let uu____1528 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1528 with
            | (env0,uu____1536) ->
                let uu____1539 = tc_comp env0 expected_c in
                (match uu____1539 with
                 | (expected_c1,uu____1547,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1552 =
                       let uu____1556 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1556 e1 in
                     (match uu____1552 with
                      | (e2,c',g') ->
                          let uu____1563 =
                            let uu____1567 =
                              let uu____1570 =
                                let uu____1571 =
                                  FStar_Syntax_Syntax.get_lazy_comp c' in
                                uu____1571 () in
                              (e2, uu____1570) in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1567 in
                          (match uu____1563 with
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
                                 let uu____1620 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1620 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | None  -> f
                                 | Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic) in
                               let uu____1625 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1625 with
                                | (e5,c,f2) ->
                                    let uu____1635 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____1635))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1639) ->
           let uu____1675 = FStar_Syntax_Util.type_u () in
           (match uu____1675 with
            | (k,u) ->
                let uu____1683 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1683 with
                 | (t1,uu____1691,f) ->
                     let uu____1693 =
                       let uu____1697 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1697 e1 in
                     (match uu____1693 with
                      | (e2,c,g) ->
                          let uu____1704 =
                            let uu____1707 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1710  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1707 e2 c f in
                          (match uu____1704 with
                           | (c1,f1) ->
                               let uu____1716 =
                                 let uu____1720 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, ((FStar_Util.Inl t1), None),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____1720 c1 in
                               (match uu____1716 with
                                | (e3,c2,f2) ->
                                    let uu____1756 =
                                      let uu____1757 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1757 in
                                    (e3, c2, uu____1756))))))
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
           let uu____1834 = FStar_Syntax_Util.head_and_args top in
           (match uu____1834 with
            | (unary_op,uu____1848) ->
                let head1 =
                  let uu____1866 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (Prims.fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1866 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1910;
              FStar_Syntax_Syntax.pos = uu____1911;
              FStar_Syntax_Syntax.vars = uu____1912;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____1938 =
               let uu____1942 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____1942 with | (env0,uu____1950) -> tc_term env0 e1 in
             match uu____1938 with
             | (e2,c,g) ->
                 let uu____1959 = FStar_Syntax_Util.head_and_args top in
                 (match uu____1959 with
                  | (reify_op,uu____1973) ->
                      let u_c =
                        let uu____1989 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____1989 with
                        | (uu____1993,c',uu____1995) ->
                            let uu____1996 =
                              let uu____1997 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____1997.FStar_Syntax_Syntax.n in
                            (match uu____1996 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2001 ->
                                 let uu____2002 = FStar_Syntax_Util.type_u () in
                                 (match uu____2002 with
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
                                            let uu____2011 =
                                              let uu____2012 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2013 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2014 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2012 uu____2013
                                                uu____2014 in
                                            failwith uu____2011);
                                       u))) in
                      let repr =
                        let uu____2016 =
                          let uu____2017 =
                            FStar_Syntax_Syntax.get_lazy_comp c in
                          uu____2017 () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2016 u_c in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2041 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2041
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2042 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2042 with
                       | (e4,c2,g') ->
                           let uu____2052 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2052)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2054;
              FStar_Syntax_Syntax.pos = uu____2055;
              FStar_Syntax_Syntax.vars = uu____2056;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2088 =
               let uu____2089 =
                 let uu____2090 =
                   let uu____2093 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2093, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2090 in
               Prims.raise uu____2089 in
             let uu____2097 = FStar_Syntax_Util.head_and_args top in
             match uu____2097 with
             | (reflect_op,uu____2111) ->
                 let uu____2126 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2126 with
                  | None  -> no_reflect ()
                  | Some ed ->
                      let uu____2132 =
                        let uu____2133 =
                          FStar_All.pipe_right
                            ed.FStar_Syntax_Syntax.qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2133 in
                      if uu____2132
                      then no_reflect ()
                      else
                        (let uu____2139 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2139 with
                         | (env_no_ex,topt) ->
                             let uu____2150 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2165 =
                                   let uu____2168 =
                                     let uu____2169 =
                                       let uu____2179 =
                                         let uu____2181 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2182 =
                                           let uu____2184 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2184] in
                                         uu____2181 :: uu____2182 in
                                       (repr, uu____2179) in
                                     FStar_Syntax_Syntax.Tm_app uu____2169 in
                                   FStar_Syntax_Syntax.mk uu____2168 in
                                 uu____2165 None top.FStar_Syntax_Syntax.pos in
                               let uu____2194 =
                                 let uu____2198 =
                                   let uu____2199 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2199 Prims.fst in
                                 tc_tot_or_gtot_term uu____2198 t in
                               match uu____2194 with
                               | (t1,uu____2216,g) ->
                                   let uu____2218 =
                                     let uu____2219 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2219.FStar_Syntax_Syntax.n in
                                   (match uu____2218 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2230,(res,uu____2232)::
                                         (wp,uu____2234)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2268 -> failwith "Impossible") in
                             (match uu____2150 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2292 =
                                    let uu____2295 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2295 with
                                    | (e2,c,g) ->
                                        ((let uu____2305 =
                                            let uu____2306 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2306 in
                                          if uu____2305
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2312 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2312 with
                                          | None  ->
                                              ((let uu____2317 =
                                                  let uu____2321 =
                                                    let uu____2324 =
                                                      let uu____2325 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2326 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2325 uu____2326 in
                                                    (uu____2324,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2321] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2317);
                                               (let uu____2331 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2331)))
                                          | Some g' ->
                                              let uu____2333 =
                                                let uu____2334 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2334 in
                                              (e2, uu____2333))) in
                                  (match uu____2292 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2341 =
                                           let uu____2342 =
                                             let uu____2343 =
                                               let uu____2344 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2344] in
                                             let uu____2345 =
                                               let uu____2351 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2351] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2343;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2345;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2342 in
                                         FStar_All.pipe_right uu____2341
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e2, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2372 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2372 with
                                        | (e4,c1,g') ->
                                            let uu____2382 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2382))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2401 =
               let uu____2402 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2402 Prims.fst in
             FStar_All.pipe_right uu____2401 instantiate_both in
           ((let uu____2411 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2411
             then
               let uu____2412 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2413 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2412
                 uu____2413
             else ());
            (let uu____2415 = tc_term (no_inst env2) head1 in
             match uu____2415 with
             | (head2,chead,g_head) ->
                 let uu____2425 =
                   let uu____2429 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2429
                   then
                     let uu____2433 = FStar_TypeChecker_Env.expected_typ env0 in
                     check_short_circuit_args env2 head2 chead g_head args
                       uu____2433
                   else
                     (let uu____2436 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env2 head2 chead g_head args
                        uu____2436) in
                 (match uu____2425 with
                  | (e1,c,g) ->
                      ((let uu____2445 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2445
                        then
                          let uu____2446 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2446
                        else ());
                       (let c1 =
                          let uu____2449 =
                            ((FStar_TypeChecker_Env.should_verify env2) &&
                               (let uu____2450 =
                                  FStar_Syntax_Util.is_lcomp_partial_return c in
                                Prims.op_Negation uu____2450))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                          if uu____2449
                          then
                            FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                              env2 e1 c
                          else c in
                        let uu____2452 = comp_check_expected_typ env0 e1 c1 in
                        match uu____2452 with
                        | (e2,c2,g') ->
                            let gimp =
                              let uu____2463 =
                                let uu____2464 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2464.FStar_Syntax_Syntax.n in
                              match uu____2463 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2468) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c2.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___94_2500 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___94_2500.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___94_2500.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___94_2500.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2525 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2527 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2527 in
                            ((let uu____2529 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2529
                              then
                                let uu____2530 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2531 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2530 uu____2531
                              else ());
                             (e2, c2, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2561 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2561 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2573 = tc_term env12 e1 in
                (match uu____2573 with
                 | (e11,c1,g1) ->
                     let uu____2583 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2589 = FStar_Syntax_Util.type_u () in
                           (match uu____2589 with
                            | (k,uu____2595) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2597 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2597, res_t)) in
                     (match uu____2583 with
                      | (env_branches,res_t) ->
                          ((let uu____2604 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2604
                            then
                              let uu____2605 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2605
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2656 =
                              let uu____2659 =
                                FStar_List.fold_right
                                  (fun uu____2678  ->
                                     fun uu____2679  ->
                                       match (uu____2678, uu____2679) with
                                       | ((uu____2711,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2744 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____2744))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2659 with
                              | (cases,g) ->
                                  let uu____2765 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____2765, g) in
                            match uu____2656 with
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
                                           (fun uu____2818  ->
                                              match uu____2818 with
                                              | ((pat,wopt,br),uu____2834,lc,uu____2836)
                                                  ->
                                                  let uu____2843 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____2843))) in
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
                                  let uu____2899 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____2899
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____2906 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____2906 in
                                     let lb =
                                       let uu____2910 =
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
                                           uu____2910;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____2914 =
                                         let uu____2917 =
                                           let uu____2918 =
                                             let uu____2926 =
                                               let uu____2927 =
                                                 let uu____2928 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____2928] in
                                               FStar_Syntax_Subst.close
                                                 uu____2927 e_match in
                                             ((false, [lb]), uu____2926) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____2918 in
                                         FStar_Syntax_Syntax.mk uu____2917 in
                                       uu____2914
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____2942 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____2942
                                  then
                                    let uu____2943 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____2944 =
                                      let uu____2945 =
                                        let uu____2946 =
                                          FStar_Syntax_Syntax.get_lazy_comp
                                            cres in
                                        uu____2946 () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____2945 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____2943 uu____2944
                                  else ());
                                 (let uu____2950 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____2950))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2953;
                FStar_Syntax_Syntax.lbunivs = uu____2954;
                FStar_Syntax_Syntax.lbtyp = uu____2955;
                FStar_Syntax_Syntax.lbeff = uu____2956;
                FStar_Syntax_Syntax.lbdef = uu____2957;_}::[]),uu____2958)
           ->
           ((let uu____2973 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____2973
             then
               let uu____2974 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____2974
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2976),uu____2977) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2987;
                FStar_Syntax_Syntax.lbunivs = uu____2988;
                FStar_Syntax_Syntax.lbtyp = uu____2989;
                FStar_Syntax_Syntax.lbeff = uu____2990;
                FStar_Syntax_Syntax.lbdef = uu____2991;_}::uu____2992),uu____2993)
           ->
           ((let uu____3009 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3009
             then
               let uu____3010 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3010
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3012),uu____3013) ->
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
          let uu____3036 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3036 with
           | (tactic1,uu____3042,uu____3043) -> Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____3078 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3078 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3091 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3091
              then FStar_Util.Inl t1
              else
                (let uu____3095 =
                   let uu____3096 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3096 in
                 FStar_Util.Inr uu____3095) in
            let is_data_ctor uu___82_3105 =
              match uu___82_3105 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____3108 -> false in
            let uu____3110 =
              (is_data_ctor dc) &&
                (let uu____3111 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3111) in
            if uu____3110
            then
              let uu____3117 =
                let uu____3118 =
                  let uu____3121 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3124 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3121, uu____3124) in
                FStar_Errors.Error uu____3118 in
              Prims.raise uu____3117
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3135 =
            let uu____3136 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3136 in
          failwith uu____3135
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3155 =
              let uu____3156 = FStar_Syntax_Subst.compress t1 in
              uu____3156.FStar_Syntax_Syntax.n in
            match uu____3155 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3159 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3167 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___95_3187 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___95_3187.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___95_3187.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___95_3187.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3215 =
            let uu____3222 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3222 with
            | None  ->
                let uu____3230 = FStar_Syntax_Util.type_u () in
                (match uu____3230 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3215 with
           | (t,uu____3251,g0) ->
               let uu____3259 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3259 with
                | (e1,uu____3270,g1) ->
                    let uu____3278 =
                      let uu____3279 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3279
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3280 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3278, uu____3280)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3282 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3291 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3291)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3282 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___96_3305 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___96_3305.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___96_3305.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3308 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3308 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3321 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3321
                       then FStar_Util.Inl t1
                       else
                         (let uu____3325 =
                            let uu____3326 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3326 in
                          FStar_Util.Inr uu____3325) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3332;
             FStar_Syntax_Syntax.pos = uu____3333;
             FStar_Syntax_Syntax.vars = uu____3334;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3342 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3342 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3364 =
                     let uu____3365 =
                       let uu____3368 = FStar_TypeChecker_Env.get_range env1 in
                       ("Unexpected number of universe instantiations",
                         uu____3368) in
                     FStar_Errors.Error uu____3365 in
                   Prims.raise uu____3364)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____3376 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___97_3378 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___98_3379 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___98_3379.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___98_3379.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___97_3378.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___97_3378.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3395 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3395 us1 in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3407 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3407 with
           | ((us,t),range) ->
               ((let uu____3425 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3425
                 then
                   let uu____3426 =
                     let uu____3427 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3427 in
                   let uu____3428 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3429 = FStar_Range.string_of_range range in
                   let uu____3430 = FStar_Range.string_of_use_range range in
                   let uu____3431 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
                     uu____3426 uu____3428 uu____3429 uu____3430 uu____3431
                 else ());
                (let fv' =
                   let uu___99_3434 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___100_3435 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___100_3435.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___100_3435.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___99_3434.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___99_3434.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3451 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3451 us in
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
          let uu____3487 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3487 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3496 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3496 with
                | (env2,uu____3504) ->
                    let uu____3507 = tc_binders env2 bs1 in
                    (match uu____3507 with
                     | (bs2,env3,g,us) ->
                         let uu____3519 = tc_comp env3 c1 in
                         (match uu____3519 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___101_3532 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___101_3532.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___101_3532.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___101_3532.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____3553 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3553 in
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
          let uu____3588 =
            let uu____3591 =
              let uu____3592 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3592] in
            FStar_Syntax_Subst.open_term uu____3591 phi in
          (match uu____3588 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____3599 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3599 with
                | (env2,uu____3607) ->
                    let uu____3610 =
                      let uu____3617 = FStar_List.hd x1 in
                      tc_binder env2 uu____3617 in
                    (match uu____3610 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3634 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____3634
                           then
                             let uu____3635 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____3636 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____3637 =
                               FStar_Syntax_Print.bv_to_string (Prims.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3635 uu____3636 uu____3637
                           else ());
                          (let uu____3639 = FStar_Syntax_Util.type_u () in
                           match uu____3639 with
                           | (t_phi,uu____3646) ->
                               let uu____3647 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____3647 with
                                | (phi2,uu____3655,f2) ->
                                    let e1 =
                                      let uu___102_3660 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x2) phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___102_3660.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___102_3660.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___102_3660.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____3679 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3679 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3688) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____3713 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____3713
            then
              let uu____3714 =
                FStar_Syntax_Print.term_to_string
                  (let uu___103_3715 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___103_3715.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___103_3715.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___103_3715.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3714
            else ());
           (let uu____3734 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____3734 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3742 ->
          let uu____3743 =
            let uu____3744 = FStar_Syntax_Print.term_to_string top in
            let uu____3745 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3744
              uu____3745 in
          failwith uu____3743
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3751 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3752,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3758,Some uu____3759) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3767 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3771 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3772 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3773 ->
          FStar_TypeChecker_Common.t_range
      | uu____3774 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____3785) ->
          let uu____3792 = FStar_Syntax_Util.type_u () in
          (match uu____3792 with
           | (k,u) ->
               let uu____3800 = tc_check_tot_or_gtot_term env t k in
               (match uu____3800 with
                | (t1,uu____3808,g) ->
                    let uu____3810 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____3810, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3812) ->
          let uu____3819 = FStar_Syntax_Util.type_u () in
          (match uu____3819 with
           | (k,u) ->
               let uu____3827 = tc_check_tot_or_gtot_term env t k in
               (match uu____3827 with
                | (t1,uu____3835,g) ->
                    let uu____3837 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____3837, u, g)))
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
            let uu____3853 =
              let uu____3854 =
                let uu____3855 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____3855 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____3854 in
            uu____3853 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____3860 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____3860 with
           | (tc1,uu____3868,f) ->
               let uu____3870 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____3870 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____3900 =
                        let uu____3901 = FStar_Syntax_Subst.compress head3 in
                        uu____3901.FStar_Syntax_Syntax.n in
                      match uu____3900 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3904,us) -> us
                      | uu____3910 -> [] in
                    let uu____3911 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____3911 with
                     | (uu____3924,args1) ->
                         let uu____3940 =
                           let uu____3952 = FStar_List.hd args1 in
                           let uu____3961 = FStar_List.tl args1 in
                           (uu____3952, uu____3961) in
                         (match uu____3940 with
                          | (res,args2) ->
                              let uu____4003 =
                                let uu____4008 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___83_4018  ->
                                          match uu___83_4018 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4024 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4024 with
                                               | (env1,uu____4031) ->
                                                   let uu____4034 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4034 with
                                                    | (e1,uu____4041,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____4008
                                  FStar_List.unzip in
                              (match uu____4003 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (Prims.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___104_4064 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___104_4064.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (Prims.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___104_4064.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4068 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4068 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____4071 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4071))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4079 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4082 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4082
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4085 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4085
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4089 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4089 Prims.snd
         | uu____4094 -> aux u)
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
            let uu____4115 =
              let uu____4116 =
                let uu____4119 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4119, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4116 in
            Prims.raise uu____4115 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4173 bs2 bs_expected1 =
              match uu____4173 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             let uu____4270 =
                               let uu____4271 =
                                 let uu____4274 =
                                   let uu____4275 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4275 in
                                 let uu____4276 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4274, uu____4276) in
                               FStar_Errors.Error uu____4271 in
                             Prims.raise uu____4270
                         | uu____4277 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4281 =
                           let uu____4284 =
                             let uu____4285 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4285.FStar_Syntax_Syntax.n in
                           match uu____4284 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4290 ->
                               ((let uu____4292 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4292
                                 then
                                   let uu____4293 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4293
                                 else ());
                                (let uu____4295 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4295 with
                                 | (t,uu____4302,g1) ->
                                     let g2 =
                                       let uu____4305 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4306 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4305
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4306 in
                                     let g3 =
                                       let uu____4308 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4308 in
                                     (t, g3))) in
                         match uu____4281 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___105_4324 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___105_4324.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___105_4324.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4333 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4333 in
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
                  | uu____4435 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4439 = tc_binders env1 bs in
                  match uu____4439 with
                  | (bs1,envbody,g,uu____4460) ->
                      let uu____4461 =
                        let uu____4468 =
                          let uu____4469 = FStar_Syntax_Subst.compress body1 in
                          uu____4469.FStar_Syntax_Syntax.n in
                        match uu____4468 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4481) ->
                            let uu____4517 = tc_comp envbody c in
                            (match uu____4517 with
                             | (c1,uu____4528,g') ->
                                 let uu____4530 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4532 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), uu____4530, body1, uu____4532))
                        | uu____4535 -> (None, None, body1, g) in
                      (match uu____4461 with
                       | (copt,tacopt,body2,g1) ->
                           (None, bs1, [], copt, tacopt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____4594 =
                    let uu____4595 = FStar_Syntax_Subst.compress t2 in
                    uu____4595.FStar_Syntax_Syntax.n in
                  match uu____4594 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4628 -> failwith "Impossible");
                       (let uu____4632 = tc_binders env1 bs in
                        match uu____4632 with
                        | (bs1,envbody,g,uu____4654) ->
                            let uu____4655 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4655 with
                             | (envbody1,uu____4674) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4686) ->
                      let uu____4691 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____4691 with
                       | (uu____4720,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4760 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____4760 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____4823 c_expected2 =
                               match uu____4823 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____4884 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____4884)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____4901 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____4901 in
                                        let uu____4902 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____4902)
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
                                               let uu____4943 =
                                                 check_binders env3 more_bs
                                                   bs_expected3 in
                                               (match uu____4943 with
                                                | (env4,bs',more1,guard',subst2)
                                                    ->
                                                    let uu____4970 =
                                                      let uu____4986 =
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          guard guard' in
                                                      (env4,
                                                        (FStar_List.append
                                                           bs2 bs'), more1,
                                                        uu____4986, subst2) in
                                                    handle_more uu____4970
                                                      c_expected3)
                                           | uu____4995 ->
                                               let uu____4996 =
                                                 let uu____4997 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____4997 in
                                               fail uu____4996 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____5013 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5013 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___106_5051 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___106_5051.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___106_5051.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___106_5051.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___106_5051.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___106_5051.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___106_5051.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___106_5051.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___106_5051.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___106_5051.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___106_5051.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___106_5051.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___106_5051.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___106_5051.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___106_5051.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___106_5051.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___106_5051.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___106_5051.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___106_5051.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___106_5051.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___106_5051.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___106_5051.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___106_5051.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___106_5051.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5065  ->
                                     fun uu____5066  ->
                                       match (uu____5065, uu____5066) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5091 =
                                             let uu____5095 =
                                               let uu____5096 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5096 Prims.fst in
                                             tc_term uu____5095 t3 in
                                           (match uu____5091 with
                                            | (t4,uu____5108,uu____5109) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5116 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___107_5117
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___107_5117.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___107_5117.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5116 ::
                                                        letrec_binders
                                                  | uu____5118 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5121 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5121 with
                            | (envbody,bs1,g,c) ->
                                let uu____5153 =
                                  let uu____5157 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5157
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5153 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), None, envbody2, body1, g))))
                  | uu____5193 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5208 = unfold_whnf env1 t2 in
                        as_function_typ true uu____5208
                      else
                        (let uu____5210 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5210 with
                         | (uu____5238,bs1,uu____5240,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, tacopt,
                               envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5265 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5265 with
          | (env1,topt) ->
              ((let uu____5277 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5277
                then
                  let uu____5278 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5278
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5282 = expected_function_typ1 env1 topt body in
                match uu____5282 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5317 =
                      tc_term
                        (let uu___108_5321 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___108_5321.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___108_5321.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___108_5321.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___108_5321.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___108_5321.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___108_5321.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___108_5321.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___108_5321.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___108_5321.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___108_5321.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___108_5321.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___108_5321.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___108_5321.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___108_5321.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___108_5321.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___108_5321.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___108_5321.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___108_5321.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___108_5321.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___108_5321.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___108_5321.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___108_5321.FStar_TypeChecker_Env.qname_and_index)
                         }) body1 in
                    (match uu____5317 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5330 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5330
                           then
                             let uu____5331 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5340 =
                               let uu____5341 =
                                 let uu____5342 =
                                   FStar_Syntax_Syntax.get_lazy_comp cbody in
                                 uu____5342 () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5341 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5331 uu____5340
                           else ());
                          (let uu____5346 =
                             let uu____5350 =
                               let uu____5353 =
                                 let uu____5354 =
                                   FStar_Syntax_Syntax.get_lazy_comp cbody in
                                 uu____5354 () in
                               (body2, uu____5353) in
                             check_expected_effect
                               (let uu___109_5357 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___109_5357.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___109_5357.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___109_5357.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___109_5357.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___109_5357.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___109_5357.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___109_5357.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___109_5357.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___109_5357.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___109_5357.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___109_5357.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___109_5357.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___109_5357.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___109_5357.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___109_5357.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___109_5357.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___109_5357.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___109_5357.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___109_5357.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___109_5357.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___109_5357.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___109_5357.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___109_5357.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5350 in
                           match uu____5346 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____5366 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5367 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5367) in
                                 if uu____5366
                                 then
                                   let uu____5368 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5368
                                 else
                                   (let guard2 =
                                      let uu____5371 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5371 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 let uu____5378 =
                                   let uu____5385 =
                                     let uu____5391 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     FStar_All.pipe_right uu____5391
                                       (fun _0_29  -> FStar_Util.Inl _0_29) in
                                   Some uu____5385 in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5378 in
                               let uu____5405 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5420 -> (e, t1, guard2)
                                      | uu____5428 ->
                                          let uu____5429 =
                                            if use_teq
                                            then
                                              let uu____5434 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5434)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5429 with
                                           | (e1,guard') ->
                                               let uu____5441 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5441)))
                                 | None  -> (e, tfun_computed, guard2) in
                               (match uu____5405 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____5454 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____5454 with
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
              (let uu____5490 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____5490
               then
                 let uu____5491 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____5492 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5491
                   uu____5492
               else ());
              (let monadic_application uu____5534 subst1 arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____5534 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___110_5575 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___110_5575.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___110_5575.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___110_5575.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____5576 =
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
                                     (fun uu___84_5603  ->
                                        match uu___84_5603 with
                                        | (uu____5612,uu____5613,FStar_Util.Inl
                                           uu____5614) -> false
                                        | (uu____5625,uu____5626,FStar_Util.Inr
                                           c) ->
                                            let uu____5636 =
                                              FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                c in
                                            Prims.op_Negation uu____5636))) in
                           let cres3 =
                             if refine_with_equality
                             then
                               let uu____5638 =
                                 (FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets))
                                   (Some
                                      ((cres2.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                   r in
                               FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                 env uu____5638 cres2
                             else
                               ((let uu____5649 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low in
                                 if uu____5649
                                 then
                                   let uu____5650 =
                                     FStar_Syntax_Print.term_to_string head2 in
                                   let uu____5651 =
                                     FStar_Syntax_Print.lcomp_to_string cres2 in
                                   let uu____5652 =
                                     FStar_TypeChecker_Rel.guard_to_string
                                       env g in
                                   FStar_Util.print3
                                     "Not refining result: f=%s; cres=%s; guard=%s\n"
                                     uu____5650 uu____5651 uu____5652
                                 else ());
                                cres2) in
                           (cres3, g)
                       | uu____5654 ->
                           let g =
                             let uu____5659 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____5659
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____5660 =
                             let uu____5661 =
                               let uu____5664 =
                                 let uu____5665 =
                                   let uu____5666 =
                                     let uu____5669 =
                                       FStar_Syntax_Syntax.get_lazy_comp
                                         cres1 in
                                     uu____5669 () in
                                   FStar_Syntax_Util.arrow bs uu____5666 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5665 in
                               FStar_Syntax_Syntax.mk_Total uu____5664 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5661 in
                           (uu____5660, g) in
                     (match uu____5576 with
                      | (cres2,guard1) ->
                          ((let uu____5680 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____5680
                            then
                              let uu____5681 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5681
                            else ());
                           (let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____5697  ->
                                     match uu____5697 with
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
                              let uu____5743 =
                                let uu____5744 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____5744.FStar_Syntax_Syntax.n in
                              match uu____5743 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____5748 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____5762  ->
                                         match uu____5762 with
                                         | (arg,uu____5774,uu____5775) -> arg
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
                                (let uu____5795 =
                                   let map_fun uu____5834 =
                                     match uu____5834 with
                                     | ((e,q),uu____5858,c0) ->
                                         (match c0 with
                                          | FStar_Util.Inl uu____5883 ->
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
                                              let uu____5926 =
                                                let uu____5929 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x in
                                                (uu____5929, q) in
                                              ((Some
                                                  (x,
                                                    (c.FStar_Syntax_Syntax.eff_name),
                                                    (c.FStar_Syntax_Syntax.res_typ),
                                                    e1)), uu____5926)) in
                                   let uu____5947 =
                                     let uu____5961 =
                                       let uu____5974 =
                                         let uu____5986 =
                                           let uu____5995 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____5995, None,
                                             (FStar_Util.Inr chead1)) in
                                         uu____5986 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____5974 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____5961 in
                                   match uu____5947 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6104 =
                                         let uu____6105 =
                                           FStar_List.hd reverse_args in
                                         Prims.fst uu____6105 in
                                       let uu____6110 =
                                         let uu____6114 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6114 in
                                       (lifted_args, uu____6104, uu____6110) in
                                 match uu____5795 with
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
                                     let bind_lifted_args e uu___85_6182 =
                                       match uu___85_6182 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6224 =
                                               let uu____6227 =
                                                 let uu____6228 =
                                                   let uu____6236 =
                                                     let uu____6237 =
                                                       let uu____6238 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6238] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6237 e in
                                                   ((false, [lb]),
                                                     uu____6236) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6228 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6227 in
                                             uu____6224 None
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
                            let uu____6272 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6272 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6330 bs args1 =
                 match uu____6330 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6425))::rest,
                         (uu____6427,None )::uu____6428) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 = check_no_escape (Some head1) env fvs t in
                          let uu____6465 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6465 with
                           | (varg,uu____6476,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6489 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6489) in
                               let uu____6490 =
                                 let uu____6512 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t1))) :: outargs), (arg ::
                                   arg_rets), uu____6512, fvs) in
                               tc_args head_info uu____6490 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____6603 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___111_6610 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___111_6610.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___111_6610.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6612 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6612
                             then
                               let uu____6613 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6613
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___112_6618 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___112_6618.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___112_6618.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___112_6618.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___112_6618.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___112_6618.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___112_6618.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___112_6618.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___112_6618.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___112_6618.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___112_6618.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___112_6618.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___112_6618.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___112_6618.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___112_6618.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___112_6618.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___112_6618.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___112_6618.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___112_6618.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___112_6618.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___112_6618.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___112_6618.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___112_6618.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___112_6618.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             (let uu____6620 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6620
                              then
                                let uu____6621 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6622 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6623 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6621 uu____6622 uu____6623
                              else ());
                             (let uu____6625 = tc_term env2 e in
                              match uu____6625 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let uu____6641 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
                                  if uu____6641
                                  then
                                    let subst2 =
                                      let uu____6646 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6646 e1 in
                                    tc_args head_info
                                      (subst2,
                                        ((arg, None,
                                           (FStar_Util.Inl
                                              ((c.FStar_Syntax_Syntax.eff_name),
                                                (c.FStar_Syntax_Syntax.res_typ))))
                                        :: outargs), (arg :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    (let uu____6702 =
                                       FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name in
                                     if uu____6702
                                     then
                                       let subst2 =
                                         let uu____6707 = FStar_List.hd bs in
                                         maybe_extend_subst subst1 uu____6707
                                           e1 in
                                       tc_args head_info
                                         (subst2,
                                           ((arg, (Some x1),
                                              (FStar_Util.Inr c)) ::
                                           outargs), (arg :: arg_rets), g1,
                                           fvs) rest rest'
                                     else
                                       (let uu____6753 =
                                          let uu____6754 = FStar_List.hd bs in
                                          FStar_Syntax_Syntax.is_null_binder
                                            uu____6754 in
                                        if uu____6753
                                        then
                                          let newx =
                                            FStar_Syntax_Syntax.new_bv
                                              (Some
                                                 (e1.FStar_Syntax_Syntax.pos))
                                              c.FStar_Syntax_Syntax.res_typ in
                                          let arg' =
                                            let uu____6763 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                newx in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____6763 in
                                          tc_args head_info
                                            (subst1,
                                              ((arg, (Some newx),
                                                 (FStar_Util.Inr c)) ::
                                              outargs), (arg' :: arg_rets),
                                              g1, fvs) rest rest'
                                        else
                                          (let uu____6801 =
                                             let uu____6823 =
                                               let uu____6825 =
                                                 let uu____6826 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x1 in
                                                 FStar_Syntax_Syntax.as_arg
                                                   uu____6826 in
                                               uu____6825 :: arg_rets in
                                             (subst1,
                                               ((arg, (Some x1),
                                                  (FStar_Util.Inr c)) ::
                                               outargs), uu____6823, g1, (x1
                                               :: fvs)) in
                                           tc_args head_info uu____6801 rest
                                             rest')))))))
                      | (uu____6863,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6884) ->
                          let uu____6914 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____6914 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6937 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____6937
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____6953 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____6953 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____6967 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____6967
                                            then
                                              let uu____6968 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____6968
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____6998 when Prims.op_Negation norm1 ->
                                     let uu____6999 = unfold_whnf env tres1 in
                                     aux true uu____6999
                                 | uu____7000 ->
                                     let uu____7001 =
                                       let uu____7002 =
                                         let uu____7005 =
                                           let uu____7006 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____7007 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____7006 uu____7007 in
                                         let uu____7011 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____7005, uu____7011) in
                                       FStar_Errors.Error uu____7002 in
                                     Prims.raise uu____7001 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app norm1 tf =
                 let uu____7027 =
                   let uu____7028 = FStar_Syntax_Util.unrefine tf in
                   uu____7028.FStar_Syntax_Syntax.n in
                 match uu____7027 with
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
                           let uu____7104 = tc_term env1 e in
                           (match uu____7104 with
                            | (e1,c,g_e) ->
                                let uu____7117 = tc_args1 env1 tl1 in
                                (match uu____7117 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7139 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7139))) in
                     let uu____7150 = tc_args1 env args in
                     (match uu____7150 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7172 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7192  ->
                                      match uu____7192 with
                                      | (uu____7200,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7172 in
                          let ml_or_tot t r1 =
                            let uu____7216 = FStar_Options.ml_ish () in
                            if uu____7216
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7219 =
                              let uu____7222 =
                                let uu____7223 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7223 Prims.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7222 in
                            ml_or_tot uu____7219 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7232 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7232
                            then
                              let uu____7233 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7234 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7235 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7233 uu____7234 uu____7235
                            else ());
                           (let uu____7238 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7238);
                           (let comp =
                              let uu____7240 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7245  ->
                                   fun out  ->
                                     match uu____7245 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7240 in
                            let uu____7254 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7261 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7254, comp, uu____7261))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7276 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7276 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | uu____7319 ->
                     if Prims.op_Negation norm1
                     then
                       let uu____7325 = unfold_whnf env tf in
                       check_function_app true uu____7325
                     else
                       (let uu____7327 =
                          let uu____7328 =
                            let uu____7331 =
                              FStar_TypeChecker_Err.expected_function_typ env
                                tf in
                            (uu____7331, (head1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____7328 in
                        Prims.raise uu____7327) in
               let uu____7337 =
                 let uu____7338 = FStar_Syntax_Util.unrefine thead in
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.WHNF] env uu____7338 in
               check_function_app false uu____7337)
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
                  let uu____7384 =
                    FStar_List.fold_left2
                      (fun uu____7397  ->
                         fun uu____7398  ->
                           fun uu____7399  ->
                             match (uu____7397, uu____7398, uu____7399) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7443 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7443 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7455 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7455 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7457 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7457) &&
                                              (let uu____7458 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7458)) in
                                       let uu____7459 =
                                         let uu____7465 =
                                           let uu____7471 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7471] in
                                         FStar_List.append seen uu____7465 in
                                       let uu____7476 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7459, uu____7476, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7384 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____7505 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7505
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7507 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7507 with | (c2,g) -> (e, c2, g)))
              | uu____7519 ->
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
        let uu____7541 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7541 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7567 = branch1 in
            (match uu____7567 with
             | (cpat,uu____7587,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7629 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0 in
                   match uu____7629 with
                   | (pat_bvs1,exps,p) ->
                       ((let uu____7651 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____7651
                         then
                           let uu____7652 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____7653 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7652 uu____7653
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____7656 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____7656 with
                         | (env1,uu____7669) ->
                             let env11 =
                               let uu___113_7673 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___113_7673.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___113_7673.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___113_7673.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___113_7673.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___113_7673.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___113_7673.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___113_7673.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___113_7673.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___113_7673.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___113_7673.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___113_7673.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___113_7673.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___113_7673.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___113_7673.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___113_7673.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___113_7673.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___113_7673.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___113_7673.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___113_7673.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___113_7673.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___113_7673.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___113_7673.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___113_7673.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             let uu____7675 =
                               let uu____7680 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____7692 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High in
                                          if uu____7692
                                          then
                                            let uu____7693 =
                                              FStar_Syntax_Print.term_to_string
                                                e in
                                            let uu____7694 =
                                              FStar_Syntax_Print.term_to_string
                                                pat_t in
                                            FStar_Util.print2
                                              "Checking pattern expression %s against expected type %s\n"
                                              uu____7693 uu____7694
                                          else ());
                                         (let uu____7696 = tc_term env11 e in
                                          match uu____7696 with
                                          | (e1,lc,g) ->
                                              ((let uu____7706 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High in
                                                if uu____7706
                                                then
                                                  let uu____7707 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env e1 in
                                                  let uu____7708 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  FStar_Util.print2
                                                    "Pre-checked pattern expression %s at type %s\n"
                                                    uu____7707 uu____7708
                                                else ());
                                               (let g' =
                                                  FStar_TypeChecker_Rel.teq
                                                    env
                                                    lc.FStar_Syntax_Syntax.res_typ
                                                    expected_pat_t in
                                                let g1 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g' in
                                                let uu____7712 =
                                                  let uu____7713 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___114_7714 = g1 in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___114_7714.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___114_7714.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___114_7714.FStar_TypeChecker_Env.implicits)
                                                       }) in
                                                  FStar_All.pipe_right
                                                    uu____7713
                                                    FStar_TypeChecker_Rel.resolve_implicits in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e1 in
                                                let uvars_to_string uvs =
                                                  let uu____7728 =
                                                    let uu____7730 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements in
                                                    FStar_All.pipe_right
                                                      uu____7730
                                                      (FStar_List.map
                                                         (fun uu____7754  ->
                                                            match uu____7754
                                                            with
                                                            | (u,uu____7759)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u)) in
                                                  FStar_All.pipe_right
                                                    uu____7728
                                                    (FStar_String.concat ", ") in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e' in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t in
                                                (let uu____7772 =
                                                   let uu____7773 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2 in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation
                                                     uu____7773 in
                                                 if uu____7772
                                                 then
                                                   let unresolved =
                                                     let uu____7780 =
                                                       FStar_Util.set_difference
                                                         uvs1 uvs2 in
                                                     FStar_All.pipe_right
                                                       uu____7780
                                                       FStar_Util.set_elements in
                                                   let uu____7794 =
                                                     let uu____7795 =
                                                       let uu____7798 =
                                                         let uu____7799 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env e' in
                                                         let uu____7800 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env
                                                             expected_pat_t in
                                                         let uu____7801 =
                                                           let uu____7802 =
                                                             FStar_All.pipe_right
                                                               unresolved
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____7814
                                                                     ->
                                                                    match uu____7814
                                                                    with
                                                                    | 
                                                                    (u,uu____7822)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u)) in
                                                           FStar_All.pipe_right
                                                             uu____7802
                                                             (FStar_String.concat
                                                                ", ") in
                                                         FStar_Util.format3
                                                           "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                           uu____7799
                                                           uu____7800
                                                           uu____7801 in
                                                       (uu____7798,
                                                         (p.FStar_Syntax_Syntax.p)) in
                                                     FStar_Errors.Error
                                                       uu____7795 in
                                                   Prims.raise uu____7794
                                                 else ());
                                                (let uu____7837 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High in
                                                 if uu____7837
                                                 then
                                                   let uu____7838 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env e1 in
                                                   FStar_Util.print1
                                                     "Done checking pattern expression %s\n"
                                                     uu____7838
                                                 else ());
                                                (e1, e')))))) in
                               FStar_All.pipe_right uu____7680
                                 FStar_List.unzip in
                             (match uu____7675 with
                              | (exps1,norm_exps) ->
                                  let p1 =
                                    FStar_TypeChecker_Util.decorate_pattern
                                      env p exps1 in
                                  (p1, pat_bvs1, pat_env, exps1, norm_exps)))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____7869 =
                   let uu____7873 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____7873
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____7869 with
                  | (scrutinee_env,uu____7886) ->
                      let uu____7889 = tc_pat true pat_t pattern in
                      (match uu____7889 with
                       | (pattern1,pat_bvs1,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____7917 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____7932 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____7932
                                 then
                                   Prims.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____7940 =
                                      let uu____7944 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____7944 e in
                                    match uu____7940 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____7917 with
                            | (when_clause1,g_when) ->
                                let uu____7964 = tc_term pat_env branch_exp in
                                (match uu____7964 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____7983 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_30  -> Some _0_30)
                                             uu____7983 in
                                     let uu____7985 =
                                       let eqs =
                                         let uu____7991 =
                                           let uu____7992 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____7992 in
                                         if uu____7991
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
                                                     | uu____8006 ->
                                                         let clause =
                                                           let uu____8008 =
                                                             env.FStar_TypeChecker_Env.universe_of
                                                               env pat_t in
                                                           FStar_Syntax_Util.mk_eq2
                                                             uu____8008 pat_t
                                                             scrutinee_tm e1 in
                                                         (match fopt with
                                                          | None  ->
                                                              Some clause
                                                          | Some f ->
                                                              let uu____8011
                                                                =
                                                                FStar_Syntax_Util.mk_disj
                                                                  clause f in
                                                              FStar_All.pipe_left
                                                                (fun _0_31 
                                                                   ->
                                                                   Some _0_31)
                                                                uu____8011))
                                                None) in
                                       let uu____8021 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____8021 with
                                       | (c1,g_branch1) ->
                                           let uu____8031 =
                                             match (eqs, when_condition) with
                                             | uu____8038 when
                                                 let uu____8043 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8043
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____8051 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8052 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8051, uu____8052)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____8059 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8059 in
                                                 let uu____8060 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8061 =
                                                   let uu____8062 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8062 g_when in
                                                 (uu____8060, uu____8061)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____8068 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8068, g_when) in
                                           (match uu____8031 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____8076 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs1 c_weak in
                                                let uu____8077 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8076, uu____8077,
                                                  g_branch1)) in
                                     (match uu____7985 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8090 =
                                              let uu____8091 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8091 in
                                            if uu____8090
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8122 =
                                                     let uu____8123 =
                                                       let uu____8124 =
                                                         let uu____8126 =
                                                           let uu____8130 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8130 in
                                                         Prims.snd uu____8126 in
                                                       FStar_List.length
                                                         uu____8124 in
                                                     uu____8123 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8122
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____8139 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8139 with
                                                     | None  -> []
                                                     | uu____8150 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None in
                                                         let disc1 =
                                                           let uu____8160 =
                                                             let uu____8161 =
                                                               let uu____8162
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8162] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8161 in
                                                           uu____8160 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8167 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool in
                                                         [uu____8167]
                                                   else [] in
                                                 let fail uu____8175 =
                                                   let uu____8176 =
                                                     let uu____8177 =
                                                       FStar_Range.string_of_range
                                                         pat_exp.FStar_Syntax_Syntax.pos in
                                                     let uu____8178 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp in
                                                     let uu____8179 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8177 uu____8178
                                                       uu____8179 in
                                                   failwith uu____8176 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8200) ->
                                                       head_constructor t1
                                                   | uu____8206 -> fail () in
                                                 let pat_exp1 =
                                                   let uu____8209 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp in
                                                   FStar_All.pipe_right
                                                     uu____8209
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
                                                     let uu____8226 =
                                                       let uu____8227 =
                                                         tc_constant
                                                           pat_exp1.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8227
                                                         scrutinee_tm1
                                                         pat_exp1 in
                                                     [uu____8226]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                   _
                                                   |FStar_Syntax_Syntax.Tm_fvar
                                                   _ ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp1 in
                                                     let uu____8235 =
                                                       let uu____8236 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8236 in
                                                     if uu____8235
                                                     then []
                                                     else
                                                       (let uu____8243 =
                                                          head_constructor
                                                            pat_exp1 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8243)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8270 =
                                                       let uu____8271 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8271 in
                                                     if uu____8270
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8280 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8296
                                                                     ->
                                                                    match uu____8296
                                                                    with
                                                                    | 
                                                                    (ei,uu____8303)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8313
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8313
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8324
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8333
                                                                    =
                                                                    let uu____8334
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None in
                                                                    let uu____8339
                                                                    =
                                                                    let uu____8340
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8340] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8334
                                                                    uu____8339 in
                                                                    uu____8333
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8280
                                                            FStar_List.flatten in
                                                        let uu____8352 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8352
                                                          sub_term_guards)
                                                 | uu____8356 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8368 =
                                                   let uu____8369 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8369 in
                                                 if uu____8368
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8372 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8372 in
                                                    let uu____8375 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8375 with
                                                    | (k,uu____8379) ->
                                                        let uu____8380 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8380
                                                         with
                                                         | (t1,uu____8385,uu____8386)
                                                             -> t1)) in
                                               let branch_guard =
                                                 let uu____8388 =
                                                   FStar_All.pipe_right
                                                     norm_disj_exps
                                                     (FStar_List.map
                                                        (build_and_check_branch_guard
                                                           scrutinee_tm)) in
                                                 FStar_All.pipe_right
                                                   uu____8388
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
                                          ((let uu____8399 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8399
                                            then
                                              let uu____8400 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8400
                                            else ());
                                           (let uu____8402 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8402, branch_guard, c1,
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
          let uu____8420 = check_let_bound_def true env1 lb in
          (match uu____8420 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8434 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then (g1, e1, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8445 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8445
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8447 =
                      let uu____8452 =
                        let uu____8458 =
                          let uu____8463 =
                            let uu____8469 =
                              let uu____8470 =
                                FStar_Syntax_Syntax.get_lazy_comp c1 in
                              uu____8470 () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8469) in
                          [uu____8463] in
                        FStar_TypeChecker_Util.generalize env1 uu____8458 in
                      FStar_List.hd uu____8452 in
                    match uu____8447 with
                    | (uu____8493,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8434 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8504 =
                      let uu____8509 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8509
                      then
                        let uu____8514 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8514 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8531 =
                                   FStar_Options.warn_top_level_effects () in
                                 if uu____8531
                                 then
                                   let uu____8532 =
                                     FStar_TypeChecker_Env.get_range env1 in
                                   FStar_Errors.warn uu____8532
                                     FStar_TypeChecker_Err.top_level_effect
                                 else ());
                                (let uu____8534 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos in
                                 (uu____8534, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8552 =
                              let uu____8553 =
                                FStar_Syntax_Syntax.get_lazy_comp c11 in
                              uu____8553 () in
                            FStar_All.pipe_right uu____8552
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8559 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8559
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____8504 with
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
                           let uu____8591 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8591,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8610 -> failwith "Impossible"
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
            let uu___115_8631 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___115_8631.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___115_8631.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___115_8631.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___115_8631.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___115_8631.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___115_8631.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___115_8631.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___115_8631.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___115_8631.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___115_8631.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___115_8631.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___115_8631.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___115_8631.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___115_8631.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___115_8631.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___115_8631.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___115_8631.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___115_8631.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___115_8631.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___115_8631.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___115_8631.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___115_8631.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___115_8631.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____8632 =
            let uu____8638 =
              let uu____8639 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8639 Prims.fst in
            check_let_bound_def false uu____8638 lb in
          (match uu____8632 with
           | (e1,uu____8651,c1,g1,annotated) ->
               let x =
                 let uu___116_8656 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___116_8656.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___116_8656.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8657 =
                 let uu____8660 =
                   let uu____8661 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8661] in
                 FStar_Syntax_Subst.open_term uu____8660 e2 in
               (match uu____8657 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = Prims.fst xbinder in
                    let uu____8673 =
                      let uu____8677 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8677 e21 in
                    (match uu____8673 with
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
                           let uu____8692 =
                             let uu____8695 =
                               let uu____8696 =
                                 let uu____8704 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8704) in
                               FStar_Syntax_Syntax.Tm_let uu____8696 in
                             FStar_Syntax_Syntax.mk uu____8695 in
                           uu____8692
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____8719 =
                             let uu____8720 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____8721 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____8720
                               c1.FStar_Syntax_Syntax.res_typ uu____8721 e11 in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8719 in
                         let g21 =
                           let uu____8723 =
                             let uu____8724 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____8724 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____8723 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____8726 =
                           let uu____8727 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____8727 in
                         if uu____8726
                         then
                           let tt =
                             let uu____8733 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____8733 FStar_Option.get in
                           ((let uu____8737 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8737
                             then
                               let uu____8738 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____8739 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____8738 uu____8739
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____8744 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8744
                             then
                               let uu____8745 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____8746 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8745 uu____8746
                             else ());
                            (e4,
                              ((let uu___117_8748 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___117_8748.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___117_8748.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___117_8748.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8749 -> failwith "Impossible"
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
          let uu____8770 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8770 with
           | (lbs1,e21) ->
               let uu____8781 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8781 with
                | (env0,topt) ->
                    let uu____8792 = build_let_rec_env true env0 lbs1 in
                    (match uu____8792 with
                     | (lbs2,rec_env) ->
                         let uu____8803 = check_let_recs rec_env lbs2 in
                         (match uu____8803 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8815 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____8815
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____8819 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____8819
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
                                     let uu____8843 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____8865 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____8865))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8843 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____8885  ->
                                           match uu____8885 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____8910 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____8910 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____8919 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____8919 with
                                | (lbs5,e22) ->
                                    let uu____8930 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____8945 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env1 g_lbs1 in
                                    (uu____8930, cres, uu____8945)))))))
      | uu____8948 -> failwith "Impossible"
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
          let uu____8969 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8969 with
           | (lbs1,e21) ->
               let uu____8980 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8980 with
                | (env0,topt) ->
                    let uu____8991 = build_let_rec_env false env0 lbs1 in
                    (match uu____8991 with
                     | (lbs2,rec_env) ->
                         let uu____9002 = check_let_recs rec_env lbs2 in
                         (match uu____9002 with
                          | (lbs3,g_lbs) ->
                              let uu____9013 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___118_9024 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___118_9024.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___118_9024.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___119_9026 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___119_9026.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___119_9026.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___119_9026.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___119_9026.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____9013 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____9043 = tc_term env2 e21 in
                                   (match uu____9043 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9054 =
                                            let uu____9055 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9055 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9054 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_comp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___120_9059 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___120_9059.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___120_9059.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___120_9059.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9060 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9060 with
                                         | (lbs5,e23) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | Some uu____9089 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres in
                                                  let cres3 =
                                                    let uu___121_9094 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___121_9094.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___121_9094.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___121_9094.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9097 -> failwith "Impossible"
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
          let uu____9113 = FStar_Syntax_Util.arrow_formals_comp t in
          match uu____9113 with
          | (uu____9119,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c) in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect) in
        let uu____9130 =
          FStar_List.fold_left
            (fun uu____9137  ->
               fun lb  ->
                 match uu____9137 with
                 | (lbs1,env1) ->
                     let uu____9149 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9149 with
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
                              (let uu____9163 =
                                 let uu____9167 =
                                   let uu____9168 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left Prims.fst uu____9168 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___122_9173 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___122_9173.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___122_9173.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___122_9173.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___122_9173.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___122_9173.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___122_9173.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___122_9173.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___122_9173.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___122_9173.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___122_9173.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___122_9173.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___122_9173.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___122_9173.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___122_9173.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___122_9173.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___122_9173.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___122_9173.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___122_9173.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___122_9173.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___122_9173.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___122_9173.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___122_9173.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___122_9173.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____9167 in
                               match uu____9163 with
                               | (t1,uu____9175,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9179 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left Prims.ignore
                                       uu____9179);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9181 =
                              (termination_check_enabled t1) &&
                                (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9181
                            then
                              let uu___123_9182 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___123_9182.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___123_9182.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___123_9182.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___123_9182.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___123_9182.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___123_9182.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___123_9182.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___123_9182.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___123_9182.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___123_9182.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___123_9182.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___123_9182.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___123_9182.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___123_9182.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___123_9182.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___123_9182.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___123_9182.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___123_9182.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___123_9182.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___123_9182.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___123_9182.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___123_9182.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___123_9182.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___124_9192 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___124_9192.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___124_9192.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9130 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9206 =
        let uu____9211 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____9222 =
                    let uu____9226 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp in
                    tc_tot_or_gtot_term uu____9226
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____9222 with
                  | (e,c,g) ->
                      ((let uu____9233 =
                          let uu____9234 = FStar_Syntax_Util.is_total_lcomp c in
                          Prims.op_Negation uu____9234 in
                        if uu____9233
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
        FStar_All.pipe_right uu____9211 FStar_List.unzip in
      match uu____9206 with
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
        let uu____9263 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9263 with
        | (env1,uu____9273) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9279 = check_lbtyp top_level env lb in
            (match uu____9279 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9305 =
                     tc_maybe_toplevel_term
                       (let uu___125_9309 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___125_9309.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___125_9309.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___125_9309.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___125_9309.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___125_9309.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___125_9309.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___125_9309.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___125_9309.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___125_9309.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___125_9309.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___125_9309.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___125_9309.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___125_9309.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___125_9309.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___125_9309.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___125_9309.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___125_9309.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___125_9309.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___125_9309.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___125_9309.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___125_9309.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___125_9309.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___125_9309.FStar_TypeChecker_Env.qname_and_index)
                        }) e11 in
                   match uu____9305 with
                   | (e12,c1,g1) ->
                       let uu____9318 =
                         let uu____9321 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9324  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9321 e12 c1 wf_annot in
                       (match uu____9318 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9334 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9334
                              then
                                let uu____9335 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9336 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9337 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9335 uu____9336 uu____9337
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
        | uu____9363 ->
            let uu____9364 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9364 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9391 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9391)
                 else
                   (let uu____9396 = FStar_Syntax_Util.type_u () in
                    match uu____9396 with
                    | (k,uu____9407) ->
                        let uu____9408 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9408 with
                         | (t2,uu____9420,g) ->
                             ((let uu____9423 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9423
                               then
                                 let uu____9424 =
                                   let uu____9425 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9425 in
                                 let uu____9426 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9424 uu____9426
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9429 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9429))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9434  ->
      match uu____9434 with
      | (x,imp) ->
          let uu____9445 = FStar_Syntax_Util.type_u () in
          (match uu____9445 with
           | (tu,u) ->
               ((let uu____9457 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9457
                 then
                   let uu____9458 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9459 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9460 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9458 uu____9459 uu____9460
                 else ());
                (let uu____9462 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9462 with
                 | (t,uu____9473,g) ->
                     let x1 =
                       ((let uu___126_9478 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___126_9478.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___126_9478.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9480 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9480
                       then
                         let uu____9481 =
                           FStar_Syntax_Print.bv_to_string (Prims.fst x1) in
                         let uu____9482 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9481 uu____9482
                       else ());
                      (let uu____9484 = push_binding env x1 in
                       (x1, uu____9484, g, u))))))
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
            let uu____9535 = tc_binder env1 b in
            (match uu____9535 with
             | (b1,env',g,u) ->
                 let uu____9558 = aux env' bs2 in
                 (match uu____9558 with
                  | (bs3,env'1,g',us) ->
                      let uu____9587 =
                        let uu____9588 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____9588 in
                      ((b1 :: bs3), env'1, uu____9587, (u :: us)))) in
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
          (fun uu____9631  ->
             fun uu____9632  ->
               match (uu____9631, uu____9632) with
               | ((t,imp),(args1,g)) ->
                   let uu____9669 = tc_term env1 t in
                   (match uu____9669 with
                    | (t1,uu____9679,g') ->
                        let uu____9681 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____9681))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9699  ->
             match uu____9699 with
             | (pats1,g) ->
                 let uu____9713 = tc_args env p in
                 (match uu____9713 with
                  | (args,g') ->
                      let uu____9721 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____9721))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____9729 = tc_maybe_toplevel_term env e in
      match uu____9729 with
      | (e1,c,g) ->
          let uu____9739 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____9739
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 =
               let uu____9746 = FStar_Syntax_Syntax.get_lazy_comp c in
               uu____9746 () in
             let c2 = norm_c env c1 in
             let uu____9750 =
               let uu____9753 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____9753
               then
                 let uu____9756 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____9756, false)
               else
                 (let uu____9758 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____9758, true)) in
             match uu____9750 with
             | (target_comp,allow_ghost) ->
                 let uu____9764 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____9764 with
                  | Some g' ->
                      let uu____9770 = FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____9770)
                  | uu____9771 ->
                      if allow_ghost
                      then
                        let uu____9776 =
                          let uu____9777 =
                            let uu____9780 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____9780, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____9777 in
                        Prims.raise uu____9776
                      else
                        (let uu____9785 =
                           let uu____9786 =
                             let uu____9789 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____9789, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____9786 in
                         Prims.raise uu____9785)))
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
      let uu____9802 = tc_tot_or_gtot_term env t in
      match uu____9802 with
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
      (let uu____9822 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9822
       then
         let uu____9823 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____9823
       else ());
      (let env1 =
         let uu___127_9826 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___127_9826.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___127_9826.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___127_9826.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___127_9826.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___127_9826.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___127_9826.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___127_9826.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___127_9826.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___127_9826.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___127_9826.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___127_9826.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___127_9826.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___127_9826.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___127_9826.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___127_9826.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___127_9826.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___127_9826.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___127_9826.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___127_9826.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___127_9826.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___127_9826.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____9829 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____9845) ->
             let uu____9846 =
               let uu____9847 =
                 let uu____9850 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____9850) in
               FStar_Errors.Error uu____9847 in
             Prims.raise uu____9846 in
       match uu____9829 with
       | (t,c,g) ->
           let uu____9860 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____9860
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____9867 =
                let uu____9868 =
                  let uu____9871 =
                    let uu____9872 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____9872 in
                  let uu____9873 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____9871, uu____9873) in
                FStar_Errors.Error uu____9868 in
              Prims.raise uu____9867))
let level_of_type_fail env e t =
  let uu____9894 =
    let uu____9895 =
      let uu____9898 =
        let uu____9899 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____9899 t in
      let uu____9900 = FStar_TypeChecker_Env.get_range env in
      (uu____9898, uu____9900) in
    FStar_Errors.Error uu____9895 in
  Prims.raise uu____9894
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____9917 =
            let uu____9918 = FStar_Syntax_Util.unrefine t1 in
            uu____9918.FStar_Syntax_Syntax.n in
          match uu____9917 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____9922 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____9925 = FStar_Syntax_Util.type_u () in
                 match uu____9925 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___130_9931 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___130_9931.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___130_9931.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___130_9931.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___130_9931.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___130_9931.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___130_9931.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___130_9931.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___130_9931.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___130_9931.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___130_9931.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___130_9931.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___130_9931.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___130_9931.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___130_9931.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___130_9931.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___130_9931.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___130_9931.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___130_9931.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___130_9931.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___130_9931.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___130_9931.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___130_9931.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___130_9931.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____9935 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____9935
                       | uu____9936 ->
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
      let uu____9945 =
        let uu____9946 = FStar_Syntax_Subst.compress e in
        uu____9946.FStar_Syntax_Syntax.n in
      match uu____9945 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____9955 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____9966) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____9991,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10006) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10013 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10013 with | ((uu____10024,t),uu____10026) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10029,(FStar_Util.Inl t,uu____10031),uu____10032) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10068,(FStar_Util.Inr c,uu____10070),uu____10071) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10118;
             FStar_Syntax_Syntax.pos = uu____10119;
             FStar_Syntax_Syntax.vars = uu____10120;_},us)
          ->
          let uu____10126 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10126 with
           | ((us',t),uu____10139) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10147 =
                     let uu____10148 =
                       let uu____10151 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10151) in
                     FStar_Errors.Error uu____10148 in
                   Prims.raise uu____10147)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____10159 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10160 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10168) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10185 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10185 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10196  ->
                      match uu____10196 with
                      | (b,uu____10200) ->
                          let uu____10201 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10201) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10206 = universe_of_aux env res in
                 level_of_type env res uu____10206 in
               let u_c =
                 let uu____10208 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10208 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10211 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10211 in
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
                let uu____10297 = universe_of_aux env hd3 in
                (uu____10297, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10307,hd4::uu____10309) ->
                let uu____10356 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____10356 with
                 | (uu____10366,uu____10367,hd5) ->
                     let uu____10383 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____10383 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10418 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____10420 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____10420 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10455 ->
                let uu____10456 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____10456 with
                 | (env1,uu____10470) ->
                     let env2 =
                       let uu___131_10474 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___131_10474.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___131_10474.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___131_10474.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___131_10474.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___131_10474.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___131_10474.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___131_10474.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___131_10474.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___131_10474.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___131_10474.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___131_10474.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___131_10474.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___131_10474.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___131_10474.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___131_10474.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___131_10474.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___131_10474.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___131_10474.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___131_10474.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___131_10474.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___131_10474.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     ((let uu____10476 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____10476
                       then
                         let uu____10477 =
                           let uu____10478 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____10478 in
                         let uu____10479 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10477 uu____10479
                       else ());
                      (let uu____10481 = tc_term env2 hd3 in
                       match uu____10481 with
                       | (uu____10494,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10495;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10497;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10498;_},g)
                           ->
                           ((let uu____10512 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____10512 Prims.ignore);
                            (t, args1))))) in
          let uu____10520 = type_of_head true hd1 args in
          (match uu____10520 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____10549 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____10549 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____10582 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____10582)))
      | FStar_Syntax_Syntax.Tm_match (uu____10585,hd1::uu____10587) ->
          let uu____10634 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____10634 with
           | (uu____10637,uu____10638,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____10654,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____10688 = universe_of_aux env e in
      level_of_type env e uu____10688
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____10701 = tc_binders env tps in
      match uu____10701 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))