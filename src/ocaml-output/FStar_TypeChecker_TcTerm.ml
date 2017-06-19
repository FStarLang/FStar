open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___87_4 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___87_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___87_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___87_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___87_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___87_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___87_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___87_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___87_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___87_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___87_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___87_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___87_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___87_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___87_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___87_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___87_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___87_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___87_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___87_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___87_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___87_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___87_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___87_4.FStar_TypeChecker_Env.qname_and_index)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___88_8 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___88_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___88_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___88_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___88_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___88_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___88_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___88_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___88_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___88_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___88_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___88_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___88_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___88_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___88_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___88_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___88_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___88_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___88_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___88_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___88_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___88_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___88_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___88_8.FStar_TypeChecker_Env.qname_and_index)
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
let is_eq: FStar_Syntax_Syntax.arg_qualifier option -> Prims.bool =
  fun uu___82_47  ->
    match uu___82_47 with
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
  FStar_Syntax_Syntax.term option ->
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
                          raise uu____114 in
                        let s =
                          let uu____120 =
                            let uu____121 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives.fst
                              uu____121 in
                          FStar_TypeChecker_Util.new_uvar env uu____120 in
                        let uu____126 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____126 with
                        | Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____130 -> fail ())) in
          aux false kt
let push_binding env b = FStar_TypeChecker_Env.push_bv env (fst b)
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
        if uu____161 then s else (FStar_Syntax_Syntax.NT ((fst b), v1)) :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___89_175 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___89_175.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___89_175.FStar_Syntax_Syntax.cflags);
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
                                   (fun _0_29  -> Some _0_29)
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
    FStar_Syntax_Syntax.comp option ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp*
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun copt  ->
      fun uu____381  ->
        match uu____381 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____401 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____401
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____403 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____403
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____405 =
              match copt with
              | Some uu____412 -> (copt, c)
              | None  ->
                  let uu____414 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Syntax_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____415 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____415)) in
                  if uu____414
                  then
                    let uu____419 =
                      let uu____421 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      Some uu____421 in
                    (uu____419, c)
                  else
                    (let uu____424 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____424
                     then let uu____428 = tot_or_gtot c in (None, uu____428)
                     else
                       (let uu____431 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____431
                        then
                          let uu____435 =
                            let uu____437 = tot_or_gtot c in Some uu____437 in
                          (uu____435, c)
                        else (None, c))) in
            (match uu____405 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | None  -> (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | Some expected_c ->
                      let uu____453 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____453 with
                       | (e1,uu____461,g) ->
                           let g1 =
                             let uu____464 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____464
                               "could not prove post-condition" g in
                           ((let uu____466 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____466
                             then
                               let uu____467 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____468 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____467 uu____468
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard env uu____490 =
  match uu____490 with
  | (te,kt,f) ->
      let uu____497 = FStar_TypeChecker_Rel.guard_form f in
      (match uu____497 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____502 =
             let uu____503 =
               let uu____506 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____507 = FStar_TypeChecker_Env.get_range env in
               (uu____506, uu____507) in
             FStar_Errors.Error uu____503 in
           raise uu____502)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____514 = FStar_TypeChecker_Env.expected_typ env in
    match uu____514 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____517 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____517
let check_smt_pat env t bs c =
  let uu____552 = FStar_Syntax_Util.is_smt_lemma t in
  if uu____552
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____553;
          FStar_Syntax_Syntax.effect_name = uu____554;
          FStar_Syntax_Syntax.result_typ = uu____555;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____559)::[];
          FStar_Syntax_Syntax.flags = uu____560;_}
        ->
        let pat_vars =
          let uu____594 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats in
          FStar_Syntax_Free.names uu____594 in
        let uu____595 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____607  ->
                  match uu____607 with
                  | (b,uu____611) ->
                      let uu____612 = FStar_Util.set_mem b pat_vars in
                      Prims.op_Negation uu____612)) in
        (match uu____595 with
         | None  -> ()
         | Some (x,uu____616) ->
             let uu____619 =
               let uu____620 = FStar_Syntax_Print.bv_to_string x in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____620 in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____619)
    | uu____621 -> failwith "Impossible"
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
        let uu____642 =
          let uu____643 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____643 in
        if uu____642
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___90_661 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___90_661.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___90_661.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___90_661.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___90_661.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___90_661.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___90_661.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___90_661.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___90_661.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___90_661.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___90_661.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___90_661.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___90_661.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___90_661.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___90_661.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___90_661.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___90_661.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___90_661.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___90_661.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___90_661.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___90_661.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___90_661.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___90_661.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___90_661.FStar_TypeChecker_Env.qname_and_index)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____684  ->
                           match uu____684 with
                           | (b,uu____689) ->
                               let t =
                                 let uu____691 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____691 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____693 -> []
                                | FStar_Syntax_Syntax.Tm_arrow uu____694 ->
                                    []
                                | uu____702 ->
                                    let uu____703 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____703]))) in
                 let as_lex_list dec =
                   let uu____708 = FStar_Syntax_Util.head_and_args dec in
                   match uu____708 with
                   | (head1,uu____719) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____735 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____738 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___83_742  ->
                           match uu___83_742 with
                           | FStar_Syntax_Syntax.DECREASES uu____743 -> true
                           | uu____746 -> false)) in
                 match uu____738 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____750 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____756 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____768 =
                 match uu____768 with
                 | (l,t) ->
                     let uu____777 =
                       let uu____778 = FStar_Syntax_Subst.compress t in
                       uu____778.FStar_Syntax_Syntax.n in
                     (match uu____777 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____811  ->
                                    match uu____811 with
                                    | (x,imp) ->
                                        let uu____818 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____818
                                        then
                                          let uu____821 =
                                            let uu____822 =
                                              let uu____824 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              Some uu____824 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____822
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____821, imp)
                                        else (x, imp))) in
                          let uu____826 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____826 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____839 =
                                   let uu____840 =
                                     let uu____841 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____842 =
                                       let uu____844 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____844] in
                                     uu____841 :: uu____842 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____840 in
                                 uu____839 None r in
                               let uu____849 = FStar_Util.prefix formals2 in
                               (match uu____849 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___91_875 = last1 in
                                      let uu____876 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___91_875.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___91_875.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____876
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____893 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____893
                                      then
                                        let uu____894 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____895 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____896 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____894 uu____895 uu____896
                                      else ());
                                     (l, t'))))
                      | uu____900 ->
                          raise
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
        (let uu___92_1172 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___92_1172.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___92_1172.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___92_1172.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___92_1172.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___92_1172.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___92_1172.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___92_1172.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___92_1172.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___92_1172.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___92_1172.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___92_1172.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___92_1172.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___92_1172.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___92_1172.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___92_1172.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___92_1172.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___92_1172.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___92_1172.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___92_1172.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___92_1172.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___92_1172.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___92_1172.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___92_1172.FStar_TypeChecker_Env.qname_and_index)
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
      (let uu____1181 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1181
       then
         let uu____1182 =
           let uu____1183 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1183 in
         let uu____1184 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1182 uu____1184
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1190 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1214 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1219 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1228 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1229 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1230 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1231 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1232 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1247 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1255 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1260 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1266 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1266 with
            | (e2,c,g) ->
                let g1 =
                  let uu___93_1277 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___93_1277.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___93_1277.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___93_1277.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1290 = FStar_Syntax_Util.type_u () in
           (match uu____1290 with
            | (t,u) ->
                let uu____1298 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1298 with
                 | (e2,c,g) ->
                     let uu____1308 =
                       let uu____1317 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1317 with
                       | (env2,uu____1330) -> tc_pats env2 pats in
                     (match uu____1308 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___94_1351 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___94_1351.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___94_1351.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___94_1351.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1352 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1363 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1352, c, uu____1363))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1371 =
             let uu____1372 = FStar_Syntax_Subst.compress e1 in
             uu____1372.FStar_Syntax_Syntax.n in
           (match uu____1371 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1378,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1380;
                               FStar_Syntax_Syntax.lbtyp = uu____1381;
                               FStar_Syntax_Syntax.lbeff = uu____1382;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1400 =
                  let uu____1404 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1404 e11 in
                (match uu____1400 with
                 | (e12,c1,g1) ->
                     let uu____1411 = tc_term env1 e2 in
                     (match uu____1411 with
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
                            let uu____1428 =
                              let uu____1431 =
                                let uu____1432 =
                                  let uu____1440 =
                                    let uu____1444 =
                                      let uu____1446 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1446] in
                                    (false, uu____1444) in
                                  (uu____1440, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1432 in
                              FStar_Syntax_Syntax.mk uu____1431 in
                            uu____1428
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
                          let uu____1476 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1476)))
            | uu____1479 ->
                let uu____1480 = tc_term env1 e1 in
                (match uu____1480 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1504) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1519 = tc_term env1 e1 in
           (match uu____1519 with
            | (e2,c,g) ->
                let e3 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1545) ->
           let uu____1581 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1581 with
            | (env0,uu____1589) ->
                let uu____1592 = tc_comp env0 expected_c in
                (match uu____1592 with
                 | (expected_c1,uu____1600,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1605 =
                       let uu____1609 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1609 e1 in
                     (match uu____1605 with
                      | (e2,c',g') ->
                          let uu____1616 =
                            let uu____1620 =
                              let uu____1623 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____1623) in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1620 in
                          (match uu____1616 with
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
                                 let uu____1674 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1674 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | None  -> f
                                 | Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic) in
                               let uu____1679 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1679 with
                                | (e5,c,f2) ->
                                    let uu____1689 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____1689))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1693) ->
           let uu____1729 = FStar_Syntax_Util.type_u () in
           (match uu____1729 with
            | (k,u) ->
                let uu____1737 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1737 with
                 | (t1,uu____1745,f) ->
                     let uu____1747 =
                       let uu____1751 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1751 e1 in
                     (match uu____1747 with
                      | (e2,c,g) ->
                          let uu____1758 =
                            let uu____1761 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1764  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1761 e2 c f in
                          (match uu____1758 with
                           | (c1,f1) ->
                               let uu____1770 =
                                 let uu____1774 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, ((FStar_Util.Inl t1), None),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____1774 c1 in
                               (match uu____1770 with
                                | (e3,c2,f2) ->
                                    let uu____1810 =
                                      let uu____1811 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1811 in
                                    (e3, c2, uu____1810))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1812;
              FStar_Syntax_Syntax.pos = uu____1813;
              FStar_Syntax_Syntax.vars = uu____1814;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1858 = FStar_Syntax_Util.head_and_args top in
           (match uu____1858 with
            | (unary_op,uu____1872) ->
                let head1 =
                  let uu____1890 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1890 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____1934);
              FStar_Syntax_Syntax.tk = uu____1935;
              FStar_Syntax_Syntax.pos = uu____1936;
              FStar_Syntax_Syntax.vars = uu____1937;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1981 = FStar_Syntax_Util.head_and_args top in
           (match uu____1981 with
            | (unary_op,uu____1995) ->
                let head1 =
                  let uu____2013 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____2013 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____2057;
              FStar_Syntax_Syntax.pos = uu____2058;
              FStar_Syntax_Syntax.vars = uu____2059;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2085 =
               let uu____2089 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____2089 with | (env0,uu____2097) -> tc_term env0 e1 in
             match uu____2085 with
             | (e2,c,g) ->
                 let uu____2106 = FStar_Syntax_Util.head_and_args top in
                 (match uu____2106 with
                  | (reify_op,uu____2120) ->
                      let u_c =
                        let uu____2136 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____2136 with
                        | (uu____2140,c',uu____2142) ->
                            let uu____2143 =
                              let uu____2144 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____2144.FStar_Syntax_Syntax.n in
                            (match uu____2143 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2148 ->
                                 let uu____2149 = FStar_Syntax_Util.type_u () in
                                 (match uu____2149 with
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
                                            let uu____2158 =
                                              let uu____2159 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2160 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2161 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2159 uu____2160
                                                uu____2161 in
                                            failwith uu____2158);
                                       u))) in
                      let repr =
                        let uu____2163 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2163 u_c in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2185 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2185
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2186 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2186 with
                       | (e4,c2,g') ->
                           let uu____2196 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2196)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2198;
              FStar_Syntax_Syntax.pos = uu____2199;
              FStar_Syntax_Syntax.vars = uu____2200;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2232 =
               let uu____2233 =
                 let uu____2234 =
                   let uu____2237 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2237, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2234 in
               raise uu____2233 in
             let uu____2241 = FStar_Syntax_Util.head_and_args top in
             match uu____2241 with
             | (reflect_op,uu____2255) ->
                 let uu____2270 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2270 with
                  | None  -> no_reflect ()
                  | Some (ed,qualifiers) ->
                      let uu____2288 =
                        let uu____2289 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2289 in
                      if uu____2288
                      then no_reflect ()
                      else
                        (let uu____2295 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2295 with
                         | (env_no_ex,topt) ->
                             let uu____2306 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2321 =
                                   let uu____2324 =
                                     let uu____2325 =
                                       let uu____2335 =
                                         let uu____2337 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2338 =
                                           let uu____2340 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2340] in
                                         uu____2337 :: uu____2338 in
                                       (repr, uu____2335) in
                                     FStar_Syntax_Syntax.Tm_app uu____2325 in
                                   FStar_Syntax_Syntax.mk uu____2324 in
                                 uu____2321 None top.FStar_Syntax_Syntax.pos in
                               let uu____2350 =
                                 let uu____2354 =
                                   let uu____2355 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2355
                                     FStar_Pervasives.fst in
                                 tc_tot_or_gtot_term uu____2354 t in
                               match uu____2350 with
                               | (t1,uu____2372,g) ->
                                   let uu____2374 =
                                     let uu____2375 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2375.FStar_Syntax_Syntax.n in
                                   (match uu____2374 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2386,(res,uu____2388)::
                                         (wp,uu____2390)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2424 -> failwith "Impossible") in
                             (match uu____2306 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2448 =
                                    let uu____2451 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2451 with
                                    | (e2,c,g) ->
                                        ((let uu____2461 =
                                            let uu____2462 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2462 in
                                          if uu____2461
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2468 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2468 with
                                          | None  ->
                                              ((let uu____2473 =
                                                  let uu____2477 =
                                                    let uu____2480 =
                                                      let uu____2481 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2482 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2481 uu____2482 in
                                                    (uu____2480,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2477] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2473);
                                               (let uu____2487 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2487)))
                                          | Some g' ->
                                              let uu____2489 =
                                                let uu____2490 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2490 in
                                              (e2, uu____2489))) in
                                  (match uu____2448 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2497 =
                                           let uu____2498 =
                                             let uu____2499 =
                                               let uu____2500 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2500] in
                                             let uu____2501 =
                                               let uu____2507 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2507] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2499;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2501;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2498 in
                                         FStar_All.pipe_right uu____2497
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e2, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2528 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2528 with
                                        | (e4,c1,g') ->
                                            let uu____2538 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2538))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2557 =
               let uu____2558 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2558 FStar_Pervasives.fst in
             FStar_All.pipe_right uu____2557 instantiate_both in
           ((let uu____2567 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2567
             then
               let uu____2568 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2569 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2568
                 uu____2569
             else ());
            (let uu____2571 = tc_term (no_inst env2) head1 in
             match uu____2571 with
             | (head2,chead,g_head) ->
                 let uu____2581 =
                   let uu____2585 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2585
                   then
                     let uu____2589 =
                       let uu____2593 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____2593 in
                     match uu____2589 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____2602 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____2603 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____2603))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____2602
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let uu____2606 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env2 head2 chead g_head args
                        uu____2606) in
                 (match uu____2581 with
                  | (e1,c,g) ->
                      ((let uu____2615 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2615
                        then
                          let uu____2616 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2616
                        else ());
                       (let uu____2618 = comp_check_expected_typ env0 e1 c in
                        match uu____2618 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____2629 =
                                let uu____2630 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2630.FStar_Syntax_Syntax.n in
                              match uu____2629 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2634) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___95_2666 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___95_2666.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___95_2666.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___95_2666.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2691 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2693 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2693 in
                            ((let uu____2695 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2695
                              then
                                let uu____2696 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2697 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2696 uu____2697
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2727 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2727 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2739 = tc_term env12 e1 in
                (match uu____2739 with
                 | (e11,c1,g1) ->
                     let uu____2749 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2755 = FStar_Syntax_Util.type_u () in
                           (match uu____2755 with
                            | (k,uu____2761) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2763 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2763, res_t)) in
                     (match uu____2749 with
                      | (env_branches,res_t) ->
                          ((let uu____2770 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2770
                            then
                              let uu____2771 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2771
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2822 =
                              let uu____2825 =
                                FStar_List.fold_right
                                  (fun uu____2844  ->
                                     fun uu____2845  ->
                                       match (uu____2844, uu____2845) with
                                       | ((uu____2877,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2910 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____2910))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2825 with
                              | (cases,g) ->
                                  let uu____2931 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____2931, g) in
                            match uu____2822 with
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
                                           (fun uu____2984  ->
                                              match uu____2984 with
                                              | ((pat,wopt,br),uu____3000,lc,uu____3002)
                                                  ->
                                                  let uu____3009 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____3009))) in
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
                                  let uu____3065 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____3065
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____3072 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____3072 in
                                     let lb =
                                       let uu____3076 =
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
                                           uu____3076;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____3080 =
                                         let uu____3083 =
                                           let uu____3084 =
                                             let uu____3092 =
                                               let uu____3093 =
                                                 let uu____3094 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____3094] in
                                               FStar_Syntax_Subst.close
                                                 uu____3093 e_match in
                                             ((false, [lb]), uu____3092) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____3084 in
                                         FStar_Syntax_Syntax.mk uu____3083 in
                                       uu____3080
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____3108 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____3108
                                  then
                                    let uu____3109 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____3110 =
                                      let uu____3111 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____3111 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____3109 uu____3110
                                  else ());
                                 (let uu____3113 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____3113))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3116;
                FStar_Syntax_Syntax.lbunivs = uu____3117;
                FStar_Syntax_Syntax.lbtyp = uu____3118;
                FStar_Syntax_Syntax.lbeff = uu____3119;
                FStar_Syntax_Syntax.lbdef = uu____3120;_}::[]),uu____3121)
           ->
           ((let uu____3136 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3136
             then
               let uu____3137 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3137
             else ());
            (let uu____3139 =
               check_top_level_let
                 (let uu___96_3143 = env1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___96_3143.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___96_3143.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___96_3143.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___96_3143.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___96_3143.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___96_3143.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___96_3143.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___96_3143.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___96_3143.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___96_3143.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___96_3143.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___96_3143.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___96_3143.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___96_3143.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___96_3143.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___96_3143.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___96_3143.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___96_3143.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___96_3143.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.type_of =
                      (uu___96_3143.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___96_3143.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___96_3143.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qname_and_index =
                      (uu___96_3143.FStar_TypeChecker_Env.qname_and_index)
                  }) top in
             match uu____3139 with
             | (lax_top,l,g) ->
                 let uu____3150 = FStar_TypeChecker_Env.should_verify env1 in
                 if uu____3150
                 then check_top_level_let env1 lax_top
                 else (lax_top, l, g)))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____3155),uu____3156) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3166;
                FStar_Syntax_Syntax.lbunivs = uu____3167;
                FStar_Syntax_Syntax.lbtyp = uu____3168;
                FStar_Syntax_Syntax.lbeff = uu____3169;
                FStar_Syntax_Syntax.lbdef = uu____3170;_}::uu____3171),uu____3172)
           ->
           ((let uu____3188 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3188
             then
               let uu____3189 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3189
             else ());
            (let uu____3191 =
               check_top_level_let_rec
                 (let uu___97_3195 = env1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___97_3195.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___97_3195.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___97_3195.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___97_3195.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___97_3195.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___97_3195.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___97_3195.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___97_3195.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___97_3195.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___97_3195.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___97_3195.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___97_3195.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___97_3195.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___97_3195.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___97_3195.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___97_3195.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___97_3195.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___97_3195.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___97_3195.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.type_of =
                      (uu___97_3195.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___97_3195.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___97_3195.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qname_and_index =
                      (uu___97_3195.FStar_TypeChecker_Env.qname_and_index)
                  }) top in
             match uu____3191 with
             | (lax_top,l,g) ->
                 let uu____3202 = FStar_TypeChecker_Env.should_verify env1 in
                 if uu____3202
                 then check_top_level_let_rec env1 lax_top
                 else (lax_top, l, g)))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3207),uu____3208) ->
           check_inner_let_rec env1 top)
and tc_tactic_opt:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option -> FStar_Syntax_Syntax.term option
  =
  fun env  ->
    fun topt  ->
      match topt with
      | None  -> None
      | Some tactic ->
          let uu____3231 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3231 with
           | (tactic1,uu____3237,uu____3238) -> Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____3273 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3273 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3286 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3286
              then FStar_Util.Inl t1
              else
                (let uu____3290 =
                   let uu____3291 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3291 in
                 FStar_Util.Inr uu____3290) in
            let is_data_ctor uu___84_3300 =
              match uu___84_3300 with
              | Some (FStar_Syntax_Syntax.Data_ctor ) -> true
              | Some (FStar_Syntax_Syntax.Record_ctor uu____3302) -> true
              | uu____3306 -> false in
            let uu____3308 =
              (is_data_ctor dc) &&
                (let uu____3309 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3309) in
            if uu____3308
            then
              let uu____3315 =
                let uu____3316 =
                  let uu____3319 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3322 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3319, uu____3322) in
                FStar_Errors.Error uu____3316 in
              raise uu____3315
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3333 =
            let uu____3334 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3334 in
          failwith uu____3333
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3353 =
              let uu____3354 = FStar_Syntax_Subst.compress t1 in
              uu____3354.FStar_Syntax_Syntax.n in
            match uu____3353 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3357 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3365 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___98_3385 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___98_3385.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___98_3385.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___98_3385.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3413 =
            let uu____3420 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3420 with
            | None  ->
                let uu____3428 = FStar_Syntax_Util.type_u () in
                (match uu____3428 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3413 with
           | (t,uu____3449,g0) ->
               let uu____3457 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3457 with
                | (e1,uu____3468,g1) ->
                    let uu____3476 =
                      let uu____3477 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3477
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3478 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3476, uu____3478)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3480 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3489 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3489)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3480 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___99_3503 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___99_3503.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___99_3503.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3506 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3506 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3519 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3519
                       then FStar_Util.Inl t1
                       else
                         (let uu____3523 =
                            let uu____3524 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3524 in
                          FStar_Util.Inr uu____3523) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3530;
             FStar_Syntax_Syntax.pos = uu____3531;
             FStar_Syntax_Syntax.vars = uu____3532;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3540 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3540 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3562 =
                     let uu____3563 =
                       let uu____3566 =
                         let uu____3567 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____3568 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____3572 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____3567 uu____3568 uu____3572 in
                       let uu____3576 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____3566, uu____3576) in
                     FStar_Errors.Error uu____3563 in
                   raise uu____3562)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____3584 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___100_3586 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___101_3587 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___101_3587.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___101_3587.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___100_3586.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___100_3586.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3603 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3603 us1 in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3615 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3615 with
           | ((us,t),range) ->
               ((let uu____3633 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3633
                 then
                   let uu____3634 =
                     let uu____3635 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3635 in
                   let uu____3636 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3637 = FStar_Range.string_of_range range in
                   let uu____3638 = FStar_Range.string_of_use_range range in
                   let uu____3639 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
                     uu____3634 uu____3636 uu____3637 uu____3638 uu____3639
                 else ());
                (let fv' =
                   let uu___102_3642 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___103_3643 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___103_3643.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___103_3643.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___102_3642.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___102_3642.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3659 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3659 us in
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
          let uu____3695 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3695 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3704 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3704 with
                | (env2,uu____3712) ->
                    let uu____3715 = tc_binders env2 bs1 in
                    (match uu____3715 with
                     | (bs2,env3,g,us) ->
                         let uu____3727 = tc_comp env3 c1 in
                         (match uu____3727 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___104_3740 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___104_3740.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___104_3740.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___104_3740.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____3761 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3761 in
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
          let uu____3796 =
            let uu____3799 =
              let uu____3800 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3800] in
            FStar_Syntax_Subst.open_term uu____3799 phi in
          (match uu____3796 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____3807 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3807 with
                | (env2,uu____3815) ->
                    let uu____3818 =
                      let uu____3825 = FStar_List.hd x1 in
                      tc_binder env2 uu____3825 in
                    (match uu____3818 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3842 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____3842
                           then
                             let uu____3843 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____3844 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____3845 =
                               FStar_Syntax_Print.bv_to_string (fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3843 uu____3844 uu____3845
                           else ());
                          (let uu____3847 = FStar_Syntax_Util.type_u () in
                           match uu____3847 with
                           | (t_phi,uu____3854) ->
                               let uu____3855 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____3855 with
                                | (phi2,uu____3863,f2) ->
                                    let e1 =
                                      let uu___105_3868 =
                                        FStar_Syntax_Util.refine (fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___105_3868.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___105_3868.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___105_3868.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____3887 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3887 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3896) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____3921 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____3921
            then
              let uu____3922 =
                FStar_Syntax_Print.term_to_string
                  (let uu___106_3923 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___106_3923.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___106_3923.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___106_3923.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3922
            else ());
           (let uu____3942 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____3942 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3950 ->
          let uu____3951 =
            let uu____3952 = FStar_Syntax_Print.term_to_string top in
            let uu____3953 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3952
              uu____3953 in
          failwith uu____3951
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3959 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3960,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3966,Some uu____3967) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3975 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3979 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3980 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3981 ->
          FStar_TypeChecker_Common.t_range
      | uu____3982 -> raise (FStar_Errors.Error ("Unsupported constant", r))
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
      | FStar_Syntax_Syntax.Total (t,uu____3993) ->
          let uu____4000 = FStar_Syntax_Util.type_u () in
          (match uu____4000 with
           | (k,u) ->
               let uu____4008 = tc_check_tot_or_gtot_term env t k in
               (match uu____4008 with
                | (t1,uu____4016,g) ->
                    let uu____4018 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____4018, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____4020) ->
          let uu____4027 = FStar_Syntax_Util.type_u () in
          (match uu____4027 with
           | (k,u) ->
               let uu____4035 = tc_check_tot_or_gtot_term env t k in
               (match uu____4035 with
                | (t1,uu____4043,g) ->
                    let uu____4045 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____4045, u, g)))
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
            let uu____4061 =
              let uu____4062 =
                let uu____4063 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____4063 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____4062 in
            uu____4061 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____4068 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____4068 with
           | (tc1,uu____4076,f) ->
               let uu____4078 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____4078 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4108 =
                        let uu____4109 = FStar_Syntax_Subst.compress head3 in
                        uu____4109.FStar_Syntax_Syntax.n in
                      match uu____4108 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4112,us) -> us
                      | uu____4118 -> [] in
                    let uu____4119 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____4119 with
                     | (uu____4132,args1) ->
                         let uu____4148 =
                           let uu____4160 = FStar_List.hd args1 in
                           let uu____4169 = FStar_List.tl args1 in
                           (uu____4160, uu____4169) in
                         (match uu____4148 with
                          | (res,args2) ->
                              let uu____4211 =
                                let uu____4216 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___85_4226  ->
                                          match uu___85_4226 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4232 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4232 with
                                               | (env1,uu____4239) ->
                                                   let uu____4242 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4242 with
                                                    | (e1,uu____4249,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____4216
                                  FStar_List.unzip in
                              (match uu____4211 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___107_4272 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___107_4272.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___107_4272.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4276 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4276 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____4279 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4279))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4287 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4288 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4292 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4292
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4295 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4295
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4299 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4299 FStar_Pervasives.snd
         | uu____4304 -> aux u)
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
            let uu____4325 =
              let uu____4326 =
                let uu____4329 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4329, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4326 in
            raise uu____4325 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4383 bs2 bs_expected1 =
              match uu____4383 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit
                            uu____4474)) ->
                             let uu____4477 =
                               let uu____4478 =
                                 let uu____4481 =
                                   let uu____4482 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4482 in
                                 let uu____4483 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4481, uu____4483) in
                               FStar_Errors.Error uu____4478 in
                             raise uu____4477
                         | (Some (FStar_Syntax_Syntax.Implicit
                            uu____4484),None ) ->
                             let uu____4487 =
                               let uu____4488 =
                                 let uu____4491 =
                                   let uu____4492 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4492 in
                                 let uu____4493 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4491, uu____4493) in
                               FStar_Errors.Error uu____4488 in
                             raise uu____4487
                         | uu____4494 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4498 =
                           let uu____4501 =
                             let uu____4502 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4502.FStar_Syntax_Syntax.n in
                           match uu____4501 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4507 ->
                               ((let uu____4509 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4509
                                 then
                                   let uu____4510 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4510
                                 else ());
                                (let uu____4512 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4512 with
                                 | (t,uu____4519,g1) ->
                                     let g2 =
                                       let uu____4522 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4523 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4522
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4523 in
                                     let g3 =
                                       let uu____4525 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4525 in
                                     (t, g3))) in
                         match uu____4498 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___108_4541 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___108_4541.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___108_4541.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4550 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4550 in
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
                  | uu____4652 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4656 = tc_binders env1 bs in
                  match uu____4656 with
                  | (bs1,envbody,g,uu____4677) ->
                      let uu____4678 =
                        let uu____4685 =
                          let uu____4686 = FStar_Syntax_Subst.compress body1 in
                          uu____4686.FStar_Syntax_Syntax.n in
                        match uu____4685 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4698) ->
                            let uu____4734 = tc_comp envbody c in
                            (match uu____4734 with
                             | (c1,uu____4745,g') ->
                                 let uu____4747 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4749 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), uu____4747, body1, uu____4749))
                        | uu____4752 -> (None, None, body1, g) in
                      (match uu____4678 with
                       | (copt,tacopt,body2,g1) ->
                           (None, bs1, [], copt, tacopt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____4811 =
                    let uu____4812 = FStar_Syntax_Subst.compress t2 in
                    uu____4812.FStar_Syntax_Syntax.n in
                  match uu____4811 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____4829 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4841 -> failwith "Impossible");
                       (let uu____4845 = tc_binders env1 bs in
                        match uu____4845 with
                        | (bs1,envbody,g,uu____4867) ->
                            let uu____4868 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4868 with
                             | (envbody1,uu____4887) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____4898;
                         FStar_Syntax_Syntax.tk = uu____4899;
                         FStar_Syntax_Syntax.pos = uu____4900;
                         FStar_Syntax_Syntax.vars = uu____4901;_},uu____4902)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4928 -> failwith "Impossible");
                       (let uu____4932 = tc_binders env1 bs in
                        match uu____4932 with
                        | (bs1,envbody,g,uu____4954) ->
                            let uu____4955 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4955 with
                             | (envbody1,uu____4974) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4986) ->
                      let uu____4991 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____4991 with
                       | (uu____5020,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____5060 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____5060 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5123 c_expected2 =
                               match uu____5123 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____5184 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____5184)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____5201 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5201 in
                                        let uu____5202 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____5202)
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
                                               let uu____5243 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____5243 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5255 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____5255 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5282 =
                                                           let uu____5298 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____5298,
                                                             subst2) in
                                                         handle_more
                                                           uu____5282
                                                           c_expected4))
                                           | uu____5307 ->
                                               let uu____5308 =
                                                 let uu____5309 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____5309 in
                                               fail uu____5308 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____5325 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5325 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___109_5363 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___109_5363.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___109_5363.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___109_5363.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___109_5363.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___109_5363.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___109_5363.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___109_5363.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___109_5363.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___109_5363.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___109_5363.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___109_5363.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___109_5363.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___109_5363.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___109_5363.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___109_5363.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___109_5363.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___109_5363.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___109_5363.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___109_5363.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___109_5363.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___109_5363.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___109_5363.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___109_5363.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5377  ->
                                     fun uu____5378  ->
                                       match (uu____5377, uu____5378) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5403 =
                                             let uu____5407 =
                                               let uu____5408 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5408
                                                 FStar_Pervasives.fst in
                                             tc_term uu____5407 t3 in
                                           (match uu____5403 with
                                            | (t4,uu____5420,uu____5421) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5428 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___110_5429
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___110_5429.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___110_5429.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5428 ::
                                                        letrec_binders
                                                  | uu____5430 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5433 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5433 with
                            | (envbody,bs1,g,c) ->
                                let uu____5465 =
                                  let uu____5469 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5469
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5465 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), None, envbody2, body1, g))))
                  | uu____5505 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5520 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5520
                      else
                        (let uu____5522 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5522 with
                         | (uu____5550,bs1,uu____5552,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, tacopt,
                               envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5577 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5577 with
          | (env1,topt) ->
              ((let uu____5589 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5589
                then
                  let uu____5590 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5590
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5594 = expected_function_typ1 env1 topt body in
                match uu____5594 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5629 =
                      tc_term
                        (let uu___111_5633 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___111_5633.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___111_5633.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___111_5633.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___111_5633.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___111_5633.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___111_5633.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___111_5633.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___111_5633.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___111_5633.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___111_5633.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___111_5633.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___111_5633.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___111_5633.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___111_5633.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___111_5633.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___111_5633.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___111_5633.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___111_5633.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___111_5633.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___111_5633.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___111_5633.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___111_5633.FStar_TypeChecker_Env.qname_and_index)
                         }) body1 in
                    (match uu____5629 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5642 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5642
                           then
                             let uu____5643 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5652 =
                               let uu____5653 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5653 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5643 uu____5652
                           else ());
                          (let uu____5655 =
                             let uu____5659 =
                               let uu____5662 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5662) in
                             check_expected_effect
                               (let uu___112_5667 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___112_5667.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___112_5667.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___112_5667.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___112_5667.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___112_5667.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___112_5667.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___112_5667.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___112_5667.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___112_5667.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___112_5667.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___112_5667.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___112_5667.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___112_5667.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___112_5667.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___112_5667.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___112_5667.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___112_5667.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___112_5667.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___112_5667.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___112_5667.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___112_5667.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___112_5667.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___112_5667.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5659 in
                           match uu____5655 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____5676 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5677 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5677) in
                                 if uu____5676
                                 then
                                   let uu____5678 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5678
                                 else
                                   (let guard2 =
                                      let uu____5681 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5681 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 let uu____5688 =
                                   let uu____5695 =
                                     let uu____5701 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     FStar_All.pipe_right uu____5701
                                       (fun _0_30  -> FStar_Util.Inl _0_30) in
                                   Some uu____5695 in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5688 in
                               let uu____5715 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5730 -> (e, t1, guard2)
                                      | uu____5738 ->
                                          let uu____5739 =
                                            if use_teq
                                            then
                                              let uu____5744 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5744)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5739 with
                                           | (e1,guard') ->
                                               let uu____5751 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5751)))
                                 | None  -> (e, tfun_computed, guard2) in
                               (match uu____5715 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____5764 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____5764 with
                                     | (c1,g1) -> (e1, c1, g1))))))))
and check_application_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
            ->
            FStar_Syntax_Syntax.typ option ->
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
              (let uu____5800 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____5800
               then
                 let uu____5801 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____5802 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5801
                   uu____5802
               else ());
              (let monadic_application uu____5840 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____5840 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___113_5877 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___113_5877.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___113_5877.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___113_5877.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____5878 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____5887 ->
                           let g =
                             let uu____5892 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____5892
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____5893 =
                             let uu____5894 =
                               let uu____5897 =
                                 let uu____5898 =
                                   let uu____5899 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____5899 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5898 in
                               FStar_Syntax_Syntax.mk_Total uu____5897 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5894 in
                           (uu____5893, g) in
                     (match uu____5878 with
                      | (cres2,guard1) ->
                          ((let uu____5910 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____5910
                            then
                              let uu____5911 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5911
                            else ());
                           (let cres3 =
                              let uu____5914 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____5914
                              then
                                let term =
                                  (FStar_Syntax_Syntax.mk_Tm_app head2
                                     (FStar_List.rev arg_rets_rev)) None
                                    head2.FStar_Syntax_Syntax.pos in
                                FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                  env term cres2
                              else cres2 in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____5937  ->
                                     match uu____5937 with
                                     | ((e,q),x,c) ->
                                         let uu____5960 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____5960
                                         then
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             (Some e) c (x, out_c)
                                         else
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             None c (x, out_c)) cres3
                                arg_comps_rev in
                            let comp1 =
                              FStar_TypeChecker_Util.bind
                                head2.FStar_Syntax_Syntax.pos env None chead1
                                (None, comp) in
                            let shortcuts_evaluation_order =
                              let uu____5969 =
                                let uu____5970 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____5970.FStar_Syntax_Syntax.n in
                              match uu____5969 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____5974 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____5984  ->
                                         match uu____5984 with
                                         | (arg,uu____5992,uu____5993) -> arg
                                             :: args1) [] arg_comps_rev in
                                let app =
                                  (FStar_Syntax_Syntax.mk_Tm_app head2 args1)
                                    (Some
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
                                (let uu____6005 =
                                   let map_fun uu____6040 =
                                     match uu____6040 with
                                     | ((e,q),uu____6060,c) ->
                                         let uu____6066 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6066
                                         then (None, (e, q))
                                         else
                                           (let x =
                                              FStar_Syntax_Syntax.new_bv None
                                                c.FStar_Syntax_Syntax.res_typ in
                                            let e1 =
                                              FStar_TypeChecker_Util.maybe_lift
                                                env e
                                                c.FStar_Syntax_Syntax.eff_name
                                                comp1.FStar_Syntax_Syntax.eff_name
                                                c.FStar_Syntax_Syntax.res_typ in
                                            let uu____6096 =
                                              let uu____6099 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____6099, q) in
                                            ((Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____6096)) in
                                   let uu____6117 =
                                     let uu____6131 =
                                       let uu____6144 =
                                         let uu____6152 =
                                           let uu____6157 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____6157, None, chead1) in
                                         uu____6152 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____6144 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6131 in
                                   match uu____6117 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6252 =
                                         let uu____6253 =
                                           FStar_List.hd reverse_args in
                                         fst uu____6253 in
                                       let uu____6258 =
                                         let uu____6262 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6262 in
                                       (lifted_args, uu____6252, uu____6258) in
                                 match uu____6005 with
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
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let app2 =
                                       FStar_TypeChecker_Util.maybe_monadic
                                         env app1
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let bind_lifted_args e uu___86_6330 =
                                       match uu___86_6330 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6372 =
                                               let uu____6375 =
                                                 let uu____6376 =
                                                   let uu____6384 =
                                                     let uu____6385 =
                                                       let uu____6386 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6386] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6385 e in
                                                   ((false, [lb]),
                                                     uu____6384) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6376 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6375 in
                                             uu____6372 None
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
                            let uu____6420 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6420 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6474 bs args1 =
                 match uu____6474 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6557))::rest,
                         (uu____6559,None )::uu____6560) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 = check_no_escape (Some head1) env fvs t in
                          let uu____6597 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6597 with
                           | (varg,uu____6608,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6621 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6621) in
                               let uu____6622 =
                                 let uu____6640 =
                                   let uu____6648 =
                                     let uu____6655 =
                                       let uu____6656 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____6656
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, None, uu____6655) in
                                   uu____6648 :: outargs in
                                 let uu____6666 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____6640, (arg :: arg_rets),
                                   uu____6666, fvs) in
                               tc_args head_info uu____6622 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit
                               uu____6726),Some (FStar_Syntax_Syntax.Implicit
                               uu____6727)) -> ()
                            | (None ,None ) -> ()
                            | (Some (FStar_Syntax_Syntax.Equality ),None ) ->
                                ()
                            | uu____6734 ->
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___114_6741 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___114_6741.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___114_6741.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6743 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6743
                             then
                               let uu____6744 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6744
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___115_6749 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___115_6749.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___115_6749.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___115_6749.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___115_6749.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___115_6749.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___115_6749.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___115_6749.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___115_6749.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___115_6749.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___115_6749.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___115_6749.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___115_6749.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___115_6749.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___115_6749.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___115_6749.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___115_6749.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___115_6749.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___115_6749.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___115_6749.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___115_6749.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___115_6749.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___115_6749.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___115_6749.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             (let uu____6751 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6751
                              then
                                let uu____6752 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6753 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6754 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6752 uu____6753 uu____6754
                              else ());
                             (let uu____6756 = tc_term env2 e in
                              match uu____6756 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____6773 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____6773 in
                                  let uu____6774 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____6774
                                  then
                                    let subst2 =
                                      let uu____6779 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6779 e1 in
                                    tc_args head_info
                                      (subst2, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        (x1 :: fvs)) rest rest'))))
                      | (uu____6827,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6848) ->
                          let uu____6878 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____6878 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6901 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____6901
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____6917 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____6917 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____6931 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____6931
                                            then
                                              let uu____6932 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____6932
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____6954 when Prims.op_Negation norm1 ->
                                     let uu____6955 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____6955
                                 | uu____6956 ->
                                     let uu____6957 =
                                       let uu____6958 =
                                         let uu____6961 =
                                           let uu____6962 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____6963 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6962 uu____6963 in
                                         let uu____6967 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____6961, uu____6967) in
                                       FStar_Errors.Error uu____6958 in
                                     raise uu____6957 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____6980 =
                   let uu____6981 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____6981.FStar_Syntax_Syntax.n in
                 match uu____6980 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____6989 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7053 = tc_term env1 e in
                           (match uu____7053 with
                            | (e1,c,g_e) ->
                                let uu____7066 = tc_args1 env1 tl1 in
                                (match uu____7066 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7088 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7088))) in
                     let uu____7099 = tc_args1 env args in
                     (match uu____7099 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7121 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7141  ->
                                      match uu____7141 with
                                      | (uu____7149,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7121 in
                          let ml_or_tot t r1 =
                            let uu____7165 = FStar_Options.ml_ish () in
                            if uu____7165
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7168 =
                              let uu____7171 =
                                let uu____7172 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7172
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7171 in
                            ml_or_tot uu____7168 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7181 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7181
                            then
                              let uu____7182 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7183 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7184 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7182 uu____7183 uu____7184
                            else ());
                           (let uu____7187 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7187);
                           (let comp =
                              let uu____7189 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7194  ->
                                   fun out  ->
                                     match uu____7194 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7189 in
                            let uu____7203 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7210 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7203, comp, uu____7210))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7213;
                        FStar_Syntax_Syntax.tk = uu____7214;
                        FStar_Syntax_Syntax.pos = uu____7215;
                        FStar_Syntax_Syntax.vars = uu____7216;_},uu____7217)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7295 = tc_term env1 e in
                           (match uu____7295 with
                            | (e1,c,g_e) ->
                                let uu____7308 = tc_args1 env1 tl1 in
                                (match uu____7308 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7330 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7330))) in
                     let uu____7341 = tc_args1 env args in
                     (match uu____7341 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7363 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7383  ->
                                      match uu____7383 with
                                      | (uu____7391,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7363 in
                          let ml_or_tot t r1 =
                            let uu____7407 = FStar_Options.ml_ish () in
                            if uu____7407
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7410 =
                              let uu____7413 =
                                let uu____7414 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7414
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7413 in
                            ml_or_tot uu____7410 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7423 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7423
                            then
                              let uu____7424 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7425 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7426 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7424 uu____7425 uu____7426
                            else ());
                           (let uu____7429 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7429);
                           (let comp =
                              let uu____7431 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7436  ->
                                   fun out  ->
                                     match uu____7436 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7431 in
                            let uu____7445 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7452 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7445, comp, uu____7452))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7467 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7467 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7503) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7509,uu____7510)
                     -> check_function_app t
                 | uu____7539 ->
                     let uu____7540 =
                       let uu____7541 =
                         let uu____7544 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7544, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7541 in
                     raise uu____7540 in
               check_function_app thead)
and check_short_circuit_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
            ->
            FStar_Syntax_Syntax.typ option ->
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
                  let uu____7595 =
                    FStar_List.fold_left2
                      (fun uu____7608  ->
                         fun uu____7609  ->
                           fun uu____7610  ->
                             match (uu____7608, uu____7609, uu____7610) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7654 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7654 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7666 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7666 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7668 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7668) &&
                                              (let uu____7669 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7669)) in
                                       let uu____7670 =
                                         let uu____7676 =
                                           let uu____7682 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7682] in
                                         FStar_List.append seen uu____7676 in
                                       let uu____7687 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7670, uu____7687, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7595 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____7716 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7716
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7718 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7718 with | (c2,g) -> (e, c2, g)))
              | uu____7730 ->
                  check_application_args env head1 chead g_head args
                    expected_topt
and tc_eqn:
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.withinfo_t*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) ->
        ((FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.term option*
          FStar_Syntax_Syntax.term)* FStar_Syntax_Syntax.term*
          FStar_Syntax_Syntax.lcomp* FStar_TypeChecker_Env.guard_t)
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____7752 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7752 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7778 = branch1 in
            (match uu____7778 with
             | (cpat,uu____7798,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7836 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____7836 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____7853 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____7853
                         then
                           let uu____7854 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____7855 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7854 uu____7855
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____7858 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____7858 with
                         | (env1,uu____7869) ->
                             let env11 =
                               let uu___116_7873 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___116_7873.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___116_7873.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___116_7873.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___116_7873.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___116_7873.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___116_7873.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___116_7873.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___116_7873.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___116_7873.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___116_7873.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___116_7873.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___116_7873.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___116_7873.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___116_7873.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___116_7873.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___116_7873.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___116_7873.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___116_7873.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___116_7873.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___116_7873.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___116_7873.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___116_7873.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___116_7873.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____7876 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____7876
                               then
                                 let uu____7877 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____7878 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____7877 uu____7878
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____7881 = tc_tot_or_gtot_term env12 exp in
                               match uu____7881 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___117_7895 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___117_7895.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___117_7895.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___117_7895.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____7896 =
                                     let g' =
                                       FStar_TypeChecker_Rel.teq env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     let g2 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g' in
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let uu____7900 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2 in
                                     FStar_All.pipe_right uu____7900
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____7911 =
                                       let uu____7912 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____7912 in
                                     if uu____7911
                                     then
                                       let unresolved =
                                         let uu____7919 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____7919
                                           FStar_Util.set_elements in
                                       let uu____7933 =
                                         let uu____7934 =
                                           let uu____7937 =
                                             let uu____7938 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____7939 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____7940 =
                                               let uu____7941 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____7953  ->
                                                         match uu____7953
                                                         with
                                                         | (u,uu____7961) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____7941
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____7938 uu____7939
                                               uu____7940 in
                                           (uu____7937,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____7934 in
                                       raise uu____7933
                                     else ());
                                    (let uu____7976 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____7976
                                     then
                                       let uu____7977 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____7977
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____7985 =
                   let uu____7989 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____7989
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____7985 with
                  | (scrutinee_env,uu____8002) ->
                      let uu____8005 = tc_pat true pat_t pattern in
                      (match uu____8005 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____8027 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____8042 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____8042
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____8050 =
                                      let uu____8054 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____8054 e in
                                    match uu____8050 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____8027 with
                            | (when_clause1,g_when) ->
                                let uu____8074 = tc_term pat_env branch_exp in
                                (match uu____8074 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____8093 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_31  -> Some _0_31)
                                             uu____8093 in
                                     let uu____8095 =
                                       let eqs =
                                         let uu____8101 =
                                           let uu____8102 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____8102 in
                                         if uu____8101
                                         then None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____8107 -> None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8116 -> None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8117 -> None
                                            | uu____8118 ->
                                                let uu____8119 =
                                                  let uu____8120 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8120 pat_t
                                                    scrutinee_tm e in
                                                Some uu____8119) in
                                       let uu____8121 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____8121 with
                                       | (c1,g_branch1) ->
                                           let uu____8131 =
                                             match (eqs, when_condition) with
                                             | uu____8138 when
                                                 let uu____8143 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8143
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____8151 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8152 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8151, uu____8152)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____8159 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8159 in
                                                 let uu____8160 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8161 =
                                                   let uu____8162 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8162 g_when in
                                                 (uu____8160, uu____8161)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____8168 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8168, g_when) in
                                           (match uu____8131 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____8176 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____8177 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8176, uu____8177,
                                                  g_branch1)) in
                                     (match uu____8095 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8190 =
                                              let uu____8191 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8191 in
                                            if uu____8190
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8222 =
                                                     let uu____8223 =
                                                       let uu____8224 =
                                                         let uu____8226 =
                                                           let uu____8230 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8230 in
                                                         snd uu____8226 in
                                                       FStar_List.length
                                                         uu____8224 in
                                                     uu____8223 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8222
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____8239 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8239 with
                                                     | None  -> []
                                                     | uu____8250 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None in
                                                         let disc1 =
                                                           let uu____8260 =
                                                             let uu____8261 =
                                                               let uu____8262
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8262] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8261 in
                                                           uu____8260 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8267 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool in
                                                         [uu____8267]
                                                   else [] in
                                                 let fail uu____8275 =
                                                   let uu____8276 =
                                                     let uu____8277 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____8278 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____8279 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8277 uu____8278
                                                       uu____8279 in
                                                   failwith uu____8276 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8300) ->
                                                       head_constructor t1
                                                   | uu____8306 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____8309 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____8309
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____8311 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____8320;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8321;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8322;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8323;_},uu____8324)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8347 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____8349 =
                                                       let uu____8350 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8350
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____8349]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8351 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8361 =
                                                       let uu____8362 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8362 in
                                                     if uu____8361
                                                     then []
                                                     else
                                                       (let uu____8369 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8369)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8375 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8381 =
                                                       let uu____8382 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8382 in
                                                     if uu____8381
                                                     then []
                                                     else
                                                       (let uu____8389 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8389)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8416 =
                                                       let uu____8417 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8417 in
                                                     if uu____8416
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8426 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8442
                                                                     ->
                                                                    match uu____8442
                                                                    with
                                                                    | 
                                                                    (ei,uu____8449)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8459
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8459
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8470
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8479
                                                                    =
                                                                    let uu____8480
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None in
                                                                    let uu____8485
                                                                    =
                                                                    let uu____8486
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8486] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8480
                                                                    uu____8485 in
                                                                    uu____8479
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8426
                                                            FStar_List.flatten in
                                                        let uu____8498 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8498
                                                          sub_term_guards)
                                                 | uu____8502 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8514 =
                                                   let uu____8515 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8515 in
                                                 if uu____8514
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8518 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8518 in
                                                    let uu____8521 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8521 with
                                                    | (k,uu____8525) ->
                                                        let uu____8526 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8526
                                                         with
                                                         | (t1,uu____8531,uu____8532)
                                                             -> t1)) in
                                               let branch_guard =
                                                 build_and_check_branch_guard
                                                   scrutinee_tm norm_pat_exp in
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
                                          ((let uu____8538 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8538
                                            then
                                              let uu____8539 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8539
                                            else ());
                                           (let uu____8541 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8541, branch_guard, c1,
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
          let uu____8559 = check_let_bound_def true env1 lb in
          (match uu____8559 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8573 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____8582 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____8582, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8585 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8585
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8587 =
                      let uu____8592 =
                        let uu____8598 =
                          let uu____8603 =
                            let uu____8611 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8611) in
                          [uu____8603] in
                        FStar_TypeChecker_Util.generalize env1 uu____8598 in
                      FStar_List.hd uu____8592 in
                    match uu____8587 with
                    | (uu____8640,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8573 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8651 =
                      let uu____8656 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8656
                      then
                        let uu____8661 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8661 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8678 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____8678
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8679 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos in
                                 (uu____8679, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8697 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8697
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8705 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8705
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____8651 with
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
                           let uu____8737 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8737,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8756 -> failwith "Impossible"
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
            let uu___118_8777 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___118_8777.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___118_8777.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___118_8777.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___118_8777.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___118_8777.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___118_8777.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___118_8777.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___118_8777.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___118_8777.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___118_8777.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___118_8777.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___118_8777.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___118_8777.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___118_8777.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___118_8777.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___118_8777.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___118_8777.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___118_8777.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___118_8777.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___118_8777.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___118_8777.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___118_8777.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___118_8777.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____8778 =
            let uu____8784 =
              let uu____8785 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8785 FStar_Pervasives.fst in
            check_let_bound_def false uu____8784 lb in
          (match uu____8778 with
           | (e1,uu____8797,c1,g1,annotated) ->
               let x =
                 let uu___119_8802 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___119_8802.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___119_8802.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8803 =
                 let uu____8806 =
                   let uu____8807 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8807] in
                 FStar_Syntax_Subst.open_term uu____8806 e2 in
               (match uu____8803 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = fst xbinder in
                    let uu____8819 =
                      let uu____8823 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8823 e21 in
                    (match uu____8819 with
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
                           let uu____8838 =
                             let uu____8841 =
                               let uu____8842 =
                                 let uu____8850 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8850) in
                               FStar_Syntax_Syntax.Tm_let uu____8842 in
                             FStar_Syntax_Syntax.mk uu____8841 in
                           uu____8838
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____8865 =
                             let uu____8866 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____8867 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____8866
                               c1.FStar_Syntax_Syntax.res_typ uu____8867 e11 in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8865 in
                         let g21 =
                           let uu____8869 =
                             let uu____8870 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____8870 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____8869 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____8872 =
                           let uu____8873 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____8873 in
                         if uu____8872
                         then
                           let tt =
                             let uu____8879 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____8879 FStar_Option.get in
                           ((let uu____8883 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8883
                             then
                               let uu____8884 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____8885 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____8884 uu____8885
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____8890 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8890
                             then
                               let uu____8891 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____8892 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8891 uu____8892
                             else ());
                            (e4,
                              ((let uu___120_8894 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___120_8894.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___120_8894.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___120_8894.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8895 -> failwith "Impossible"
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
          let uu____8916 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8916 with
           | (lbs1,e21) ->
               let uu____8927 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8927 with
                | (env0,topt) ->
                    let uu____8938 = build_let_rec_env true env0 lbs1 in
                    (match uu____8938 with
                     | (lbs2,rec_env) ->
                         let uu____8949 = check_let_recs rec_env lbs2 in
                         (match uu____8949 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8961 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____8961
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____8965 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____8965
                                  (fun _0_33  -> Some _0_33) in
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
                                     let uu____8990 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____9012 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____9012))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8990 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____9032  ->
                                           match uu____9032 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____9057 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____9057 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____9066 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____9066 with
                                | (lbs5,e22) ->
                                    ((let uu____9078 =
                                        FStar_TypeChecker_Rel.discharge_guard
                                          env1 g_lbs1 in
                                      FStar_All.pipe_right uu____9078
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1));
                                     (let uu____9079 =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_let
                                              ((true, lbs5), e22)))
                                          (Some
                                             (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos in
                                      (uu____9079, cres,
                                        FStar_TypeChecker_Rel.trivial_guard)))))))))
      | uu____9096 -> failwith "Impossible"
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
          let uu____9117 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9117 with
           | (lbs1,e21) ->
               let uu____9128 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9128 with
                | (env0,topt) ->
                    let uu____9139 = build_let_rec_env false env0 lbs1 in
                    (match uu____9139 with
                     | (lbs2,rec_env) ->
                         let uu____9150 = check_let_recs rec_env lbs2 in
                         (match uu____9150 with
                          | (lbs3,g_lbs) ->
                              let uu____9161 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___121_9172 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___121_9172.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___121_9172.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___122_9174 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___122_9174.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___122_9174.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___122_9174.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___122_9174.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____9161 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____9191 = tc_term env2 e21 in
                                   (match uu____9191 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9202 =
                                            let uu____9203 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9203 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9202 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___123_9207 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___123_9207.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___123_9207.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___123_9207.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9208 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9208 with
                                         | (lbs5,e23) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | Some uu____9237 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres in
                                                  let cres3 =
                                                    let uu___124_9242 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___124_9242.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___124_9242.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___124_9242.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9245 -> failwith "Impossible"
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
        let termination_check_enabled lbname lbdef lbtyp =
          let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
          let uu____9268 =
            let uu____9271 =
              let uu____9272 = FStar_Syntax_Subst.compress t in
              uu____9272.FStar_Syntax_Syntax.n in
            let uu____9275 =
              let uu____9276 = FStar_Syntax_Subst.compress lbdef in
              uu____9276.FStar_Syntax_Syntax.n in
            (uu____9271, uu____9275) in
          match uu____9268 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9282,uu____9283)) ->
              let actuals1 =
                let uu____9317 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9317
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____9335 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9335) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____9347 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____9347) in
                  let msg =
                    let uu____9352 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____9353 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9352 uu____9353 formals_msg actuals_msg in
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____9358 ->
              let uu____9361 =
                let uu____9362 =
                  let uu____9365 =
                    let uu____9366 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____9367 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9366 uu____9367 in
                  (uu____9365, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____9362 in
              raise uu____9361 in
        let uu____9368 =
          FStar_List.fold_left
            (fun uu____9375  ->
               fun lb  ->
                 match uu____9375 with
                 | (lbs1,env1) ->
                     let uu____9387 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9387 with
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
                              (let uu____9401 =
                                 let uu____9405 =
                                   let uu____9406 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left FStar_Pervasives.fst
                                     uu____9406 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___125_9411 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___125_9411.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___125_9411.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___125_9411.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___125_9411.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___125_9411.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___125_9411.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___125_9411.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___125_9411.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___125_9411.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___125_9411.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___125_9411.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___125_9411.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___125_9411.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___125_9411.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___125_9411.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___125_9411.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___125_9411.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___125_9411.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___125_9411.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___125_9411.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___125_9411.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___125_9411.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___125_9411.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____9405 in
                               match uu____9401 with
                               | (t1,uu____9413,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9417 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9417);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9419 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9419
                            then
                              let uu___126_9420 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___126_9420.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___126_9420.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___126_9420.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___126_9420.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___126_9420.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___126_9420.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___126_9420.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___126_9420.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___126_9420.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___126_9420.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___126_9420.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___126_9420.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___126_9420.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___126_9420.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___126_9420.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___126_9420.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___126_9420.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___126_9420.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___126_9420.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___126_9420.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___126_9420.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___126_9420.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___126_9420.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___127_9430 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___127_9430.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___127_9430.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9368 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9444 =
        let uu____9449 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9461 =
                     let uu____9462 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____9462.FStar_Syntax_Syntax.n in
                   match uu____9461 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9465 -> ()
                   | uu____9480 ->
                       let uu____9481 =
                         let uu____9482 =
                           let uu____9485 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____9485) in
                         FStar_Errors.Error uu____9482 in
                       raise uu____9481);
                  (let uu____9486 =
                     let uu____9490 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____9490
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____9486 with
                   | (e,c,g) ->
                       ((let uu____9497 =
                           let uu____9498 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____9498 in
                         if uu____9497
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
                             FStar_Syntax_Const.effect_Tot_lid e in
                         (lb1, g)))))) in
        FStar_All.pipe_right uu____9449 FStar_List.unzip in
      match uu____9444 with
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
        let uu____9527 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9527 with
        | (env1,uu____9537) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9543 = check_lbtyp top_level env lb in
            (match uu____9543 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9569 =
                     tc_maybe_toplevel_term
                       (let uu___128_9573 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___128_9573.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___128_9573.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___128_9573.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___128_9573.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___128_9573.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___128_9573.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___128_9573.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___128_9573.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___128_9573.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___128_9573.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___128_9573.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___128_9573.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___128_9573.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___128_9573.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___128_9573.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___128_9573.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___128_9573.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___128_9573.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___128_9573.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___128_9573.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___128_9573.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___128_9573.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___128_9573.FStar_TypeChecker_Env.qname_and_index)
                        }) e11 in
                   match uu____9569 with
                   | (e12,c1,g1) ->
                       let uu____9582 =
                         let uu____9585 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9588  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9585 e12 c1 wf_annot in
                       (match uu____9582 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9598 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9598
                              then
                                let uu____9599 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9600 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9601 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9599 uu____9600 uu____9601
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))
and check_lbtyp:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ option* FStar_TypeChecker_Env.guard_t*
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
        | uu____9627 ->
            let uu____9628 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9628 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9655 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9655)
                 else
                   (let uu____9660 = FStar_Syntax_Util.type_u () in
                    match uu____9660 with
                    | (k,uu____9671) ->
                        let uu____9672 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9672 with
                         | (t2,uu____9684,g) ->
                             ((let uu____9687 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9687
                               then
                                 let uu____9688 =
                                   let uu____9689 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9689 in
                                 let uu____9690 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9688 uu____9690
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9693 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9693))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9698  ->
      match uu____9698 with
      | (x,imp) ->
          let uu____9709 = FStar_Syntax_Util.type_u () in
          (match uu____9709 with
           | (tu,u) ->
               ((let uu____9721 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9721
                 then
                   let uu____9722 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9723 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9724 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9722 uu____9723 uu____9724
                 else ());
                (let uu____9726 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9726 with
                 | (t,uu____9737,g) ->
                     let x1 =
                       ((let uu___129_9742 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___129_9742.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___129_9742.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9744 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9744
                       then
                         let uu____9745 =
                           FStar_Syntax_Print.bv_to_string (fst x1) in
                         let uu____9746 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9745 uu____9746
                       else ());
                      (let uu____9748 = push_binding env x1 in
                       (x1, uu____9748, g, u))))))
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
            let uu____9799 = tc_binder env1 b in
            (match uu____9799 with
             | (b1,env',g,u) ->
                 let uu____9822 = aux env' bs2 in
                 (match uu____9822 with
                  | (bs3,env'1,g',us) ->
                      let uu____9851 =
                        let uu____9852 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____9852 in
                      ((b1 :: bs3), env'1, uu____9851, (u :: us)))) in
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
          (fun uu____9895  ->
             fun uu____9896  ->
               match (uu____9895, uu____9896) with
               | ((t,imp),(args1,g)) ->
                   let uu____9933 = tc_term env1 t in
                   (match uu____9933 with
                    | (t1,uu____9943,g') ->
                        let uu____9945 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____9945))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9963  ->
             match uu____9963 with
             | (pats1,g) ->
                 let uu____9977 = tc_args env p in
                 (match uu____9977 with
                  | (args,g') ->
                      let uu____9985 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____9985))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____9993 = tc_maybe_toplevel_term env e in
      match uu____9993 with
      | (e1,c,g) ->
          let uu____10003 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____10003
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____10013 =
               let uu____10016 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____10016
               then
                 let uu____10019 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____10019, false)
               else
                 (let uu____10021 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____10021, true)) in
             match uu____10013 with
             | (target_comp,allow_ghost) ->
                 let uu____10027 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____10027 with
                  | Some g' ->
                      let uu____10033 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____10033)
                  | uu____10034 ->
                      if allow_ghost
                      then
                        let uu____10039 =
                          let uu____10040 =
                            let uu____10043 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____10043, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____10040 in
                        raise uu____10039
                      else
                        (let uu____10048 =
                           let uu____10049 =
                             let uu____10052 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____10052, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____10049 in
                         raise uu____10048)))
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
      let uu____10065 = tc_tot_or_gtot_term env t in
      match uu____10065 with
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
      (let uu____10085 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10085
       then
         let uu____10086 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____10086
       else ());
      (let env1 =
         let uu___130_10089 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___130_10089.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___130_10089.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___130_10089.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___130_10089.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___130_10089.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___130_10089.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___130_10089.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___130_10089.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___130_10089.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___130_10089.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___130_10089.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___130_10089.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___130_10089.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___130_10089.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___130_10089.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___130_10089.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___130_10089.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___130_10089.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___130_10089.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___130_10089.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___130_10089.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____10092 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10108) ->
             let uu____10109 =
               let uu____10110 =
                 let uu____10113 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____10113) in
               FStar_Errors.Error uu____10110 in
             raise uu____10109 in
       match uu____10092 with
       | (t,c,g) ->
           let uu____10123 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____10123
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10130 =
                let uu____10131 =
                  let uu____10134 =
                    let uu____10135 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10135 in
                  let uu____10136 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____10134, uu____10136) in
                FStar_Errors.Error uu____10131 in
              raise uu____10130))
let level_of_type_fail env e t =
  let uu____10157 =
    let uu____10158 =
      let uu____10161 =
        let uu____10162 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10162 t in
      let uu____10163 = FStar_TypeChecker_Env.get_range env in
      (uu____10161, uu____10163) in
    FStar_Errors.Error uu____10158 in
  raise uu____10157
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____10180 =
            let uu____10181 = FStar_Syntax_Util.unrefine t1 in
            uu____10181.FStar_Syntax_Syntax.n in
          match uu____10180 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10185 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____10188 = FStar_Syntax_Util.type_u () in
                 match uu____10188 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___133_10194 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___133_10194.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___133_10194.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___133_10194.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___133_10194.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___133_10194.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___133_10194.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___133_10194.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___133_10194.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___133_10194.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___133_10194.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___133_10194.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___133_10194.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___133_10194.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___133_10194.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___133_10194.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___133_10194.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___133_10194.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___133_10194.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___133_10194.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___133_10194.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___133_10194.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___133_10194.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___133_10194.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____10198 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____10198
                       | uu____10199 ->
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
      let uu____10208 =
        let uu____10209 = FStar_Syntax_Subst.compress e in
        uu____10209.FStar_Syntax_Syntax.n in
      match uu____10208 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10214 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10219 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10242 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10253) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10278,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10293) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10300 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10300 with | ((uu____10311,t),uu____10313) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10316,(FStar_Util.Inl t,uu____10318),uu____10319) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10355,(FStar_Util.Inr c,uu____10357),uu____10358) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)) None
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10401;
             FStar_Syntax_Syntax.pos = uu____10402;
             FStar_Syntax_Syntax.vars = uu____10403;_},us)
          ->
          let uu____10409 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10409 with
           | ((us',t),uu____10422) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10430 =
                     let uu____10431 =
                       let uu____10434 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10434) in
                     FStar_Errors.Error uu____10431 in
                   raise uu____10430)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____10442 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10443 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10451) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10468 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10468 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10479  ->
                      match uu____10479 with
                      | (b,uu____10483) ->
                          let uu____10484 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10484) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10489 = universe_of_aux env res in
                 level_of_type env res uu____10489 in
               let u_c =
                 let uu____10491 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10491 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10494 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10494 in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us)) in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u) None
                 e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2 in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____10564 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10574 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10604 ->
                let uu____10605 = universe_of_aux env hd3 in
                (uu____10605, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10615 ->
                let uu____10616 = universe_of_aux env hd3 in
                (uu____10616, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10626 ->
                let uu____10635 = universe_of_aux env hd3 in
                (uu____10635, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10645 ->
                let uu____10650 = universe_of_aux env hd3 in
                (uu____10650, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10660 ->
                let uu____10678 = universe_of_aux env hd3 in
                (uu____10678, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10688 ->
                let uu____10693 = universe_of_aux env hd3 in
                (uu____10693, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10703 ->
                let uu____10704 = universe_of_aux env hd3 in
                (uu____10704, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10714 ->
                let uu____10722 = universe_of_aux env hd3 in
                (uu____10722, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____10732 ->
                let uu____10737 = universe_of_aux env hd3 in
                (uu____10737, args1)
            | FStar_Syntax_Syntax.Tm_type uu____10747 ->
                let uu____10748 = universe_of_aux env hd3 in
                (uu____10748, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10758,hd4::uu____10760) ->
                let uu____10807 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____10807 with
                 | (uu____10817,uu____10818,hd5) ->
                     let uu____10834 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____10834 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10869 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____10871 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____10871 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10906 ->
                let uu____10907 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____10907 with
                 | (env1,uu____10921) ->
                     let env2 =
                       let uu___134_10925 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___134_10925.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___134_10925.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___134_10925.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___134_10925.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___134_10925.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___134_10925.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___134_10925.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___134_10925.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___134_10925.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___134_10925.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___134_10925.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___134_10925.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___134_10925.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___134_10925.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___134_10925.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___134_10925.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___134_10925.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___134_10925.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___134_10925.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___134_10925.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___134_10925.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     ((let uu____10927 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____10927
                       then
                         let uu____10928 =
                           let uu____10929 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____10929 in
                         let uu____10930 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10928 uu____10930
                       else ());
                      (let uu____10932 = tc_term env2 hd3 in
                       match uu____10932 with
                       | (uu____10945,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10946;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10948;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10949;_},g)
                           ->
                           ((let uu____10959 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____10959
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____10967 = type_of_head true hd1 args in
          (match uu____10967 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____10996 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____10996 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____11029 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____11029)))
      | FStar_Syntax_Syntax.Tm_match (uu____11032,hd1::uu____11034) ->
          let uu____11081 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____11081 with
           | (uu____11084,uu____11085,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11101,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____11135 = universe_of_aux env e in
      level_of_type env e uu____11135
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____11148 = tc_binders env tps in
      match uu____11148 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))