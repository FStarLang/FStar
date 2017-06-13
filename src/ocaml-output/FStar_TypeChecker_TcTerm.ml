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
       | FStar_Syntax_Syntax.Tm_bvar uu____1230 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1231 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1232 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1233 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1234 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1249 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1257 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1262 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1268 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1268 with
            | (e2,c,g) ->
                let g1 =
                  let uu___93_1279 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___93_1279.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___93_1279.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___93_1279.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1292 = FStar_Syntax_Util.type_u () in
           (match uu____1292 with
            | (t,u) ->
                let uu____1300 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1300 with
                 | (e2,c,g) ->
                     let uu____1310 =
                       let uu____1319 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1319 with
                       | (env2,uu____1332) -> tc_pats env2 pats in
                     (match uu____1310 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___94_1353 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___94_1353.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___94_1353.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___94_1353.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1354 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1365 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1354, c, uu____1365))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1373 =
             let uu____1374 = FStar_Syntax_Subst.compress e1 in
             uu____1374.FStar_Syntax_Syntax.n in
           (match uu____1373 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1380,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1382;
                               FStar_Syntax_Syntax.lbtyp = uu____1383;
                               FStar_Syntax_Syntax.lbeff = uu____1384;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1402 =
                  let uu____1406 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1406 e11 in
                (match uu____1402 with
                 | (e12,c1,g1) ->
                     let uu____1413 = tc_term env1 e2 in
                     (match uu____1413 with
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
                            let uu____1430 =
                              let uu____1433 =
                                let uu____1434 =
                                  let uu____1442 =
                                    let uu____1446 =
                                      let uu____1448 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1448] in
                                    (false, uu____1446) in
                                  (uu____1442, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1434 in
                              FStar_Syntax_Syntax.mk uu____1433 in
                            uu____1430
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
                          let uu____1478 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1478)))
            | uu____1481 ->
                let uu____1482 = tc_term env1 e1 in
                (match uu____1482 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1506) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1521 = tc_term env1 e1 in
           (match uu____1521 with
            | (e2,c,g) ->
                let e3 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1547) ->
           let uu____1583 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1583 with
            | (env0,uu____1591) ->
                let uu____1594 = tc_comp env0 expected_c in
                (match uu____1594 with
                 | (expected_c1,uu____1602,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1607 =
                       let uu____1611 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1611 e1 in
                     (match uu____1607 with
                      | (e2,c',g') ->
                          let uu____1618 =
                            let uu____1622 =
                              let uu____1625 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____1625) in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1622 in
                          (match uu____1618 with
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
                                 let uu____1676 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1676 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | None  -> f
                                 | Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic) in
                               let uu____1681 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1681 with
                                | (e5,c,f2) ->
                                    let uu____1691 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____1691))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1695) ->
           let uu____1731 = FStar_Syntax_Util.type_u () in
           (match uu____1731 with
            | (k,u) ->
                let uu____1739 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1739 with
                 | (t1,uu____1747,f) ->
                     let uu____1749 =
                       let uu____1753 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1753 e1 in
                     (match uu____1749 with
                      | (e2,c,g) ->
                          let uu____1760 =
                            let uu____1763 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1766  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1763 e2 c f in
                          (match uu____1760 with
                           | (c1,f1) ->
                               let uu____1772 =
                                 let uu____1776 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, ((FStar_Util.Inl t1), None),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____1776 c1 in
                               (match uu____1772 with
                                | (e3,c2,f2) ->
                                    let uu____1812 =
                                      let uu____1813 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1813 in
                                    (e3, c2, uu____1812))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1814;
              FStar_Syntax_Syntax.pos = uu____1815;
              FStar_Syntax_Syntax.vars = uu____1816;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1860 = FStar_Syntax_Util.head_and_args top in
           (match uu____1860 with
            | (unary_op,uu____1874) ->
                let head1 =
                  let uu____1892 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1892 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____1936);
              FStar_Syntax_Syntax.tk = uu____1937;
              FStar_Syntax_Syntax.pos = uu____1938;
              FStar_Syntax_Syntax.vars = uu____1939;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1983 = FStar_Syntax_Util.head_and_args top in
           (match uu____1983 with
            | (unary_op,uu____1997) ->
                let head1 =
                  let uu____2015 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____2015 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____2059;
              FStar_Syntax_Syntax.pos = uu____2060;
              FStar_Syntax_Syntax.vars = uu____2061;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2087 =
               let uu____2091 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____2091 with | (env0,uu____2099) -> tc_term env0 e1 in
             match uu____2087 with
             | (e2,c,g) ->
                 let uu____2108 = FStar_Syntax_Util.head_and_args top in
                 (match uu____2108 with
                  | (reify_op,uu____2122) ->
                      let u_c =
                        let uu____2138 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____2138 with
                        | (uu____2142,c',uu____2144) ->
                            let uu____2145 =
                              let uu____2146 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____2146.FStar_Syntax_Syntax.n in
                            (match uu____2145 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2150 ->
                                 let uu____2151 = FStar_Syntax_Util.type_u () in
                                 (match uu____2151 with
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
                                            let uu____2160 =
                                              let uu____2161 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2162 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2163 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2161 uu____2162
                                                uu____2163 in
                                            failwith uu____2160);
                                       u))) in
                      let repr =
                        let uu____2165 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2165 u_c in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2187 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2187
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2188 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2188 with
                       | (e4,c2,g') ->
                           let uu____2198 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2198)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2200;
              FStar_Syntax_Syntax.pos = uu____2201;
              FStar_Syntax_Syntax.vars = uu____2202;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2234 =
               let uu____2235 =
                 let uu____2236 =
                   let uu____2239 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2239, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2236 in
               raise uu____2235 in
             let uu____2243 = FStar_Syntax_Util.head_and_args top in
             match uu____2243 with
             | (reflect_op,uu____2257) ->
                 let uu____2272 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2272 with
                  | None  -> no_reflect ()
                  | Some (ed,qualifiers) ->
                      let uu____2290 =
                        let uu____2291 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2291 in
                      if uu____2290
                      then no_reflect ()
                      else
                        (let uu____2297 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2297 with
                         | (env_no_ex,topt) ->
                             let uu____2308 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2323 =
                                   let uu____2326 =
                                     let uu____2327 =
                                       let uu____2337 =
                                         let uu____2339 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2340 =
                                           let uu____2342 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2342] in
                                         uu____2339 :: uu____2340 in
                                       (repr, uu____2337) in
                                     FStar_Syntax_Syntax.Tm_app uu____2327 in
                                   FStar_Syntax_Syntax.mk uu____2326 in
                                 uu____2323 None top.FStar_Syntax_Syntax.pos in
                               let uu____2352 =
                                 let uu____2356 =
                                   let uu____2357 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2357
                                     FStar_Pervasives.fst in
                                 tc_tot_or_gtot_term uu____2356 t in
                               match uu____2352 with
                               | (t1,uu____2374,g) ->
                                   let uu____2376 =
                                     let uu____2377 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2377.FStar_Syntax_Syntax.n in
                                   (match uu____2376 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2388,(res,uu____2390)::
                                         (wp,uu____2392)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2426 -> failwith "Impossible") in
                             (match uu____2308 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2450 =
                                    let uu____2453 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2453 with
                                    | (e2,c,g) ->
                                        ((let uu____2463 =
                                            let uu____2464 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2464 in
                                          if uu____2463
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2470 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2470 with
                                          | None  ->
                                              ((let uu____2475 =
                                                  let uu____2479 =
                                                    let uu____2482 =
                                                      let uu____2483 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2484 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2483 uu____2484 in
                                                    (uu____2482,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2479] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2475);
                                               (let uu____2489 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2489)))
                                          | Some g' ->
                                              let uu____2491 =
                                                let uu____2492 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2492 in
                                              (e2, uu____2491))) in
                                  (match uu____2450 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2499 =
                                           let uu____2500 =
                                             let uu____2501 =
                                               let uu____2502 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2502] in
                                             let uu____2503 =
                                               let uu____2509 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2509] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2501;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2503;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2500 in
                                         FStar_All.pipe_right uu____2499
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e2, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2530 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2530 with
                                        | (e4,c1,g') ->
                                            let uu____2540 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2540))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2559 =
               let uu____2560 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2560 FStar_Pervasives.fst in
             FStar_All.pipe_right uu____2559 instantiate_both in
           ((let uu____2569 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2569
             then
               let uu____2570 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2571 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2570
                 uu____2571
             else ());
            (let uu____2573 = tc_term (no_inst env2) head1 in
             match uu____2573 with
             | (head2,chead,g_head) ->
                 let uu____2583 =
                   let uu____2587 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2587
                   then
                     let uu____2591 =
                       let uu____2595 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____2595 in
                     match uu____2591 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____2604 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____2605 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____2605))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____2604
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let uu____2608 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env2 head2 chead g_head args
                        uu____2608) in
                 (match uu____2583 with
                  | (e1,c,g) ->
                      ((let uu____2617 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2617
                        then
                          let uu____2618 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2618
                        else ());
                       (let uu____2620 = comp_check_expected_typ env0 e1 c in
                        match uu____2620 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____2631 =
                                let uu____2632 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2632.FStar_Syntax_Syntax.n in
                              match uu____2631 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2636) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___95_2676 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___95_2676.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___95_2676.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___95_2676.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2705 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2707 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2707 in
                            ((let uu____2709 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2709
                              then
                                let uu____2710 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2711 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2710 uu____2711
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2741 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2741 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2753 = tc_term env12 e1 in
                (match uu____2753 with
                 | (e11,c1,g1) ->
                     let uu____2763 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2769 = FStar_Syntax_Util.type_u () in
                           (match uu____2769 with
                            | (k,uu____2775) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2777 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2777, res_t)) in
                     (match uu____2763 with
                      | (env_branches,res_t) ->
                          ((let uu____2784 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2784
                            then
                              let uu____2785 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2785
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2836 =
                              let uu____2839 =
                                FStar_List.fold_right
                                  (fun uu____2858  ->
                                     fun uu____2859  ->
                                       match (uu____2858, uu____2859) with
                                       | ((uu____2891,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2924 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____2924))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2839 with
                              | (cases,g) ->
                                  let uu____2945 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____2945, g) in
                            match uu____2836 with
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
                                           (fun uu____2998  ->
                                              match uu____2998 with
                                              | ((pat,wopt,br),uu____3014,lc,uu____3016)
                                                  ->
                                                  let uu____3023 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____3023))) in
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
                                  let uu____3079 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____3079
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____3086 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____3086 in
                                     let lb =
                                       let uu____3090 =
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
                                           uu____3090;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____3094 =
                                         let uu____3097 =
                                           let uu____3098 =
                                             let uu____3106 =
                                               let uu____3107 =
                                                 let uu____3108 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____3108] in
                                               FStar_Syntax_Subst.close
                                                 uu____3107 e_match in
                                             ((false, [lb]), uu____3106) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____3098 in
                                         FStar_Syntax_Syntax.mk uu____3097 in
                                       uu____3094
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____3122 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____3122
                                  then
                                    let uu____3123 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____3124 =
                                      let uu____3125 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____3125 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____3123 uu____3124
                                  else ());
                                 (let uu____3127 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____3127))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3130;
                FStar_Syntax_Syntax.lbunivs = uu____3131;
                FStar_Syntax_Syntax.lbtyp = uu____3132;
                FStar_Syntax_Syntax.lbeff = uu____3133;
                FStar_Syntax_Syntax.lbdef = uu____3134;_}::[]),uu____3135)
           ->
           ((let uu____3150 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3150
             then
               let uu____3151 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3151
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____3153),uu____3154) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3164;
                FStar_Syntax_Syntax.lbunivs = uu____3165;
                FStar_Syntax_Syntax.lbtyp = uu____3166;
                FStar_Syntax_Syntax.lbeff = uu____3167;
                FStar_Syntax_Syntax.lbdef = uu____3168;_}::uu____3169),uu____3170)
           ->
           ((let uu____3186 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3186
             then
               let uu____3187 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3187
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3189),uu____3190) ->
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
          let uu____3213 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3213 with
           | (tactic1,uu____3219,uu____3220) -> Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____3255 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3255 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3268 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3268
              then FStar_Util.Inl t1
              else
                (let uu____3272 =
                   let uu____3273 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3273 in
                 FStar_Util.Inr uu____3272) in
            let is_data_ctor uu___84_3282 =
              match uu___84_3282 with
              | Some (FStar_Syntax_Syntax.Data_ctor ) -> true
              | Some (FStar_Syntax_Syntax.Record_ctor uu____3284) -> true
              | uu____3288 -> false in
            let uu____3290 =
              (is_data_ctor dc) &&
                (let uu____3291 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3291) in
            if uu____3290
            then
              let uu____3297 =
                let uu____3298 =
                  let uu____3301 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3304 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3301, uu____3304) in
                FStar_Errors.Error uu____3298 in
              raise uu____3297
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3315 =
            let uu____3316 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3316 in
          failwith uu____3315
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3339 =
              let uu____3340 = FStar_Syntax_Subst.compress t1 in
              uu____3340.FStar_Syntax_Syntax.n in
            match uu____3339 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3343 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3351 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___96_3375 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___96_3375.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___96_3375.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___96_3375.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3407 =
            let uu____3414 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3414 with
            | None  ->
                let uu____3422 = FStar_Syntax_Util.type_u () in
                (match uu____3422 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3407 with
           | (t,uu____3443,g0) ->
               let uu____3451 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3451 with
                | (e1,uu____3462,g1) ->
                    let uu____3470 =
                      let uu____3471 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3471
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3472 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3470, uu____3472)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3474 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3483 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3483)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3474 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___97_3497 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___97_3497.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___97_3497.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3500 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3500 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3513 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3513
                       then FStar_Util.Inl t1
                       else
                         (let uu____3517 =
                            let uu____3518 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3518 in
                          FStar_Util.Inr uu____3517) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3524;
             FStar_Syntax_Syntax.pos = uu____3525;
             FStar_Syntax_Syntax.vars = uu____3526;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3534 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3534 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
<<<<<<< HEAD
                  (let uu____3556 =
                     let uu____3557 =
                       let uu____3560 = FStar_TypeChecker_Env.get_range env1 in
                       ("Unexpected number of universe instantiations",
                         uu____3560) in
                     FStar_Errors.Error uu____3557 in
                   raise uu____3556)
=======
                  (let uu____3530 =
                     let uu____3531 =
                       let uu____3534 =
                         let uu____3535 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____3536 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____3540 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____3535 uu____3536 uu____3540 in
                       let uu____3544 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____3534, uu____3544) in
                     FStar_Errors.Error uu____3531 in
                   raise uu____3530)
>>>>>>> origin/master
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
<<<<<<< HEAD
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____3569 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___98_3571 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___99_3572 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___99_3572.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___99_3572.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___98_3571.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___98_3571.FStar_Syntax_Syntax.fv_qual)
=======
                             FStar_Unionfind.change u'' (Some u)
                         | uu____3552 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___98_3554 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___99_3555 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___99_3555.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___99_3555.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___98_3554.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___98_3554.FStar_Syntax_Syntax.fv_qual)
>>>>>>> origin/master
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
<<<<<<< HEAD
                    let uu____3588 =
=======
                    let uu____3571 =
>>>>>>> origin/master
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3588 us1 in
=======
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3571 us1 in
>>>>>>> origin/master
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
<<<<<<< HEAD
          let uu____3600 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3600 with
           | ((us,t),range) ->
               ((let uu____3618 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3618
                 then
                   let uu____3619 =
                     let uu____3620 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3620 in
                   let uu____3621 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3622 = FStar_Range.string_of_range range in
                   let uu____3623 = FStar_Range.string_of_use_range range in
                   let uu____3624 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____3619 uu____3621 uu____3622 uu____3623 uu____3624
                 else ());
                (let fv' =
                   let uu___100_3627 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___101_3628 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___101_3628.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___101_3628.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___100_3627.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___100_3627.FStar_Syntax_Syntax.fv_qual)
=======
          let uu____3583 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3583 with
           | ((us,t),range) ->
               ((let uu____3601 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3601
                 then
                   let uu____3602 =
                     let uu____3603 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3603 in
                   let uu____3604 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3605 = FStar_Range.string_of_range range in
                   let uu____3606 = FStar_Range.string_of_use_range range in
                   let uu____3607 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
                     uu____3602 uu____3604 uu____3605 uu____3606 uu____3607
                 else ());
                (let fv' =
                   let uu___100_3610 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___101_3611 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___101_3611.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___101_3611.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___100_3610.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___100_3610.FStar_Syntax_Syntax.fv_qual)
>>>>>>> origin/master
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
<<<<<<< HEAD
                    let uu____3644 =
=======
                    let uu____3627 =
>>>>>>> origin/master
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3644 us in
=======
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3627 us in
>>>>>>> origin/master
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
<<<<<<< HEAD
          let uu____3680 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3680 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3689 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3689 with
                | (env2,uu____3697) ->
                    let uu____3700 = tc_binders env2 bs1 in
                    (match uu____3700 with
                     | (bs2,env3,g,us) ->
                         let uu____3712 = tc_comp env3 c1 in
                         (match uu____3712 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___102_3725 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___102_3725.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___102_3725.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___102_3725.FStar_Syntax_Syntax.vars)
=======
          let uu____3663 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3663 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3672 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3672 with
                | (env2,uu____3680) ->
                    let uu____3683 = tc_binders env2 bs1 in
                    (match uu____3683 with
                     | (bs2,env3,g,us) ->
                         let uu____3695 = tc_comp env3 c1 in
                         (match uu____3695 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___102_3708 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___102_3708.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___102_3708.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___102_3708.FStar_Syntax_Syntax.vars)
>>>>>>> origin/master
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
<<<<<<< HEAD
                                  let uu____3746 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3746 in
=======
                                  let uu____3729 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3729 in
>>>>>>> origin/master
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
<<<<<<< HEAD
          let uu____3781 =
            let uu____3784 =
              let uu____3785 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3785] in
            FStar_Syntax_Subst.open_term uu____3784 phi in
          (match uu____3781 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____3792 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3792 with
                | (env2,uu____3800) ->
                    let uu____3803 =
                      let uu____3810 = FStar_List.hd x1 in
                      tc_binder env2 uu____3810 in
                    (match uu____3803 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3827 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____3827
                           then
                             let uu____3828 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____3829 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____3830 =
                               FStar_Syntax_Print.bv_to_string (fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3828 uu____3829 uu____3830
                           else ());
                          (let uu____3832 = FStar_Syntax_Util.type_u () in
                           match uu____3832 with
                           | (t_phi,uu____3839) ->
                               let uu____3840 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____3840 with
                                | (phi2,uu____3848,f2) ->
                                    let e1 =
                                      let uu___103_3853 =
=======
          let uu____3764 =
            let uu____3767 =
              let uu____3768 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3768] in
            FStar_Syntax_Subst.open_term uu____3767 phi in
          (match uu____3764 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____3775 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3775 with
                | (env2,uu____3783) ->
                    let uu____3786 =
                      let uu____3793 = FStar_List.hd x1 in
                      tc_binder env2 uu____3793 in
                    (match uu____3786 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3810 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____3810
                           then
                             let uu____3811 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____3812 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____3813 =
                               FStar_Syntax_Print.bv_to_string (fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3811 uu____3812 uu____3813
                           else ());
                          (let uu____3815 = FStar_Syntax_Util.type_u () in
                           match uu____3815 with
                           | (t_phi,uu____3822) ->
                               let uu____3823 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____3823 with
                                | (phi2,uu____3831,f2) ->
                                    let e1 =
                                      let uu___103_3836 =
>>>>>>> origin/master
                                        FStar_Syntax_Util.refine (fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
<<<<<<< HEAD
                                          (uu___103_3853.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___103_3853.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___103_3853.FStar_Syntax_Syntax.vars)
=======
                                          (uu___103_3836.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___103_3836.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___103_3836.FStar_Syntax_Syntax.vars)
>>>>>>> origin/master
                                      } in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos in
                                    let g =
<<<<<<< HEAD
                                      let uu____3872 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3872 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3881) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____3906 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____3906
            then
              let uu____3907 =
                FStar_Syntax_Print.term_to_string
                  (let uu___104_3908 = top in
=======
                                      let uu____3855 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3855 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3864) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____3889 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____3889
            then
              let uu____3890 =
                FStar_Syntax_Print.term_to_string
                  (let uu___104_3891 = top in
>>>>>>> origin/master
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
<<<<<<< HEAD
                       (uu___104_3908.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___104_3908.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___104_3908.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3907
            else ());
           (let uu____3927 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____3927 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3935 ->
          let uu____3936 =
            let uu____3937 = FStar_Syntax_Print.term_to_string top in
            let uu____3938 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3937
              uu____3938 in
          failwith uu____3936
=======
                       (uu___104_3891.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___104_3891.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___104_3891.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3890
            else ());
           (let uu____3910 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____3910 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3918 ->
          let uu____3919 =
            let uu____3920 = FStar_Syntax_Print.term_to_string top in
            let uu____3921 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3920
              uu____3921 in
          failwith uu____3919
>>>>>>> origin/master
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
<<<<<<< HEAD
      | FStar_Const.Const_bool uu____3944 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3945,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3951,Some uu____3952) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3960 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3964 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3965 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3966 ->
          FStar_TypeChecker_Common.t_range
      | uu____3967 -> raise (FStar_Errors.Error ("Unsupported constant", r))
=======
      | FStar_Const.Const_bool uu____3927 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3928,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3934,Some uu____3935) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3943 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3947 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3948 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3949 ->
          FStar_TypeChecker_Common.t_range
      | uu____3950 -> raise (FStar_Errors.Error ("Unsupported constant", r))
>>>>>>> origin/master
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
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Total (t,uu____3978) ->
          let uu____3985 = FStar_Syntax_Util.type_u () in
          (match uu____3985 with
           | (k,u) ->
               let uu____3993 = tc_check_tot_or_gtot_term env t k in
               (match uu____3993 with
                | (t1,uu____4001,g) ->
                    let uu____4003 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____4003, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____4005) ->
          let uu____4012 = FStar_Syntax_Util.type_u () in
          (match uu____4012 with
           | (k,u) ->
               let uu____4020 = tc_check_tot_or_gtot_term env t k in
               (match uu____4020 with
                | (t1,uu____4028,g) ->
                    let uu____4030 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____4030, u, g)))
=======
      | FStar_Syntax_Syntax.Total (t,uu____3961) ->
          let uu____3968 = FStar_Syntax_Util.type_u () in
          (match uu____3968 with
           | (k,u) ->
               let uu____3976 = tc_check_tot_or_gtot_term env t k in
               (match uu____3976 with
                | (t1,uu____3984,g) ->
                    let uu____3986 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____3986, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3988) ->
          let uu____3995 = FStar_Syntax_Util.type_u () in
          (match uu____3995 with
           | (k,u) ->
               let uu____4003 = tc_check_tot_or_gtot_term env t k in
               (match uu____4003 with
                | (t1,uu____4011,g) ->
                    let uu____4013 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____4013, u, g)))
>>>>>>> origin/master
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
<<<<<<< HEAD
            let uu____4046 =
              let uu____4047 =
                let uu____4048 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____4048 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____4047 in
            uu____4046 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____4053 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____4053 with
           | (tc1,uu____4061,f) ->
               let uu____4063 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____4063 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4093 =
                        let uu____4094 = FStar_Syntax_Subst.compress head3 in
                        uu____4094.FStar_Syntax_Syntax.n in
                      match uu____4093 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4097,us) -> us
                      | uu____4103 -> [] in
                    let uu____4104 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____4104 with
                     | (uu____4117,args1) ->
                         let uu____4133 =
                           let uu____4145 = FStar_List.hd args1 in
                           let uu____4154 = FStar_List.tl args1 in
                           (uu____4145, uu____4154) in
                         (match uu____4133 with
                          | (res,args2) ->
                              let uu____4196 =
                                let uu____4201 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___85_4211  ->
                                          match uu___85_4211 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4217 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4217 with
                                               | (env1,uu____4224) ->
                                                   let uu____4227 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4227 with
                                                    | (e1,uu____4234,g) ->
=======
            let uu____4029 =
              let uu____4030 =
                let uu____4031 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____4031 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____4030 in
            uu____4029 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____4036 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____4036 with
           | (tc1,uu____4044,f) ->
               let uu____4046 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____4046 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4076 =
                        let uu____4077 = FStar_Syntax_Subst.compress head3 in
                        uu____4077.FStar_Syntax_Syntax.n in
                      match uu____4076 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4080,us) -> us
                      | uu____4086 -> [] in
                    let uu____4087 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____4087 with
                     | (uu____4100,args1) ->
                         let uu____4116 =
                           let uu____4128 = FStar_List.hd args1 in
                           let uu____4137 = FStar_List.tl args1 in
                           (uu____4128, uu____4137) in
                         (match uu____4116 with
                          | (res,args2) ->
                              let uu____4179 =
                                let uu____4184 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___85_4194  ->
                                          match uu___85_4194 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4200 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4200 with
                                               | (env1,uu____4207) ->
                                                   let uu____4210 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4210 with
                                                    | (e1,uu____4217,g) ->
>>>>>>> origin/master
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
<<<<<<< HEAD
                                FStar_All.pipe_right uu____4201
                                  FStar_List.unzip in
                              (match uu____4196 with
=======
                                FStar_All.pipe_right uu____4184
                                  FStar_List.unzip in
                              (match uu____4179 with
>>>>>>> origin/master
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
<<<<<<< HEAD
                                       (let uu___105_4257 = c1 in
=======
                                       (let uu___105_4240 = c1 in
>>>>>>> origin/master
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
<<<<<<< HEAD
                                            (uu___105_4257.FStar_Syntax_Syntax.effect_name);
=======
                                            (uu___105_4240.FStar_Syntax_Syntax.effect_name);
>>>>>>> origin/master
                                          FStar_Syntax_Syntax.result_typ =
                                            (fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
<<<<<<< HEAD
                                            (uu___105_4257.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4261 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4261 with
=======
                                            (uu___105_4240.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4244 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4244 with
>>>>>>> origin/master
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
<<<<<<< HEAD
                                   let uu____4264 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4264))))))
=======
                                   let uu____4247 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4247))))))
>>>>>>> origin/master
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
<<<<<<< HEAD
        | FStar_Syntax_Syntax.U_bvar uu____4272 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4273 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4279 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4279
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4282 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4282
=======
        | FStar_Syntax_Syntax.U_bvar uu____4255 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4256 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4260 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4260
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4263 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4263
>>>>>>> origin/master
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
<<<<<<< HEAD
             let uu____4286 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4286 FStar_Pervasives.snd
         | uu____4291 -> aux u)
=======
             let uu____4267 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4267 FStar_Pervasives.snd
         | uu____4272 -> aux u)
>>>>>>> origin/master
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
<<<<<<< HEAD
            let uu____4312 =
              let uu____4313 =
                let uu____4316 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4316, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4313 in
            raise uu____4312 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4370 bs2 bs_expected1 =
              match uu____4370 with
=======
            let uu____4293 =
              let uu____4294 =
                let uu____4297 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4297, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4294 in
            raise uu____4293 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4351 bs2 bs_expected1 =
              match uu____4351 with
>>>>>>> origin/master
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit
<<<<<<< HEAD
                            uu____4461)) ->
                             let uu____4464 =
                               let uu____4465 =
                                 let uu____4468 =
                                   let uu____4469 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4469 in
                                 let uu____4470 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4468, uu____4470) in
                               FStar_Errors.Error uu____4465 in
                             raise uu____4464
                         | (Some (FStar_Syntax_Syntax.Implicit
                            uu____4471),None ) ->
                             let uu____4474 =
                               let uu____4475 =
                                 let uu____4478 =
                                   let uu____4479 =
=======
                            uu____4442)) ->
                             let uu____4445 =
                               let uu____4446 =
                                 let uu____4449 =
                                   let uu____4450 =
>>>>>>> origin/master
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4479 in
                                 let uu____4480 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
<<<<<<< HEAD
                                 (uu____4478, uu____4480) in
                               FStar_Errors.Error uu____4475 in
                             raise uu____4474
                         | uu____4481 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4485 =
                           let uu____4488 =
                             let uu____4489 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4489.FStar_Syntax_Syntax.n in
                           match uu____4488 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4494 ->
                               ((let uu____4496 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4496
                                 then
                                   let uu____4497 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4497
                                 else ());
                                (let uu____4499 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4499 with
                                 | (t,uu____4506,g1) ->
                                     let g2 =
                                       let uu____4509 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4510 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4509
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4510 in
                                     let g3 =
                                       let uu____4512 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4512 in
                                     (t, g3))) in
                         match uu____4485 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___106_4528 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___106_4528.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___106_4528.FStar_Syntax_Syntax.index);
=======
                                 (uu____4449, uu____4451) in
                               FStar_Errors.Error uu____4446 in
                             raise uu____4445
                         | (Some (FStar_Syntax_Syntax.Implicit
                            uu____4452),None ) ->
                             let uu____4455 =
                               let uu____4456 =
                                 let uu____4459 =
                                   let uu____4460 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4460 in
                                 let uu____4461 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4459, uu____4461) in
                               FStar_Errors.Error uu____4456 in
                             raise uu____4455
                         | uu____4462 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4466 =
                           let uu____4469 =
                             let uu____4470 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4470.FStar_Syntax_Syntax.n in
                           match uu____4469 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4475 ->
                               ((let uu____4477 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4477
                                 then
                                   let uu____4478 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4478
                                 else ());
                                (let uu____4480 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4480 with
                                 | (t,uu____4487,g1) ->
                                     let g2 =
                                       let uu____4490 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4491 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4490
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4491 in
                                     let g3 =
                                       let uu____4493 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4493 in
                                     (t, g3))) in
                         match uu____4466 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___106_4509 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___106_4509.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___106_4509.FStar_Syntax_Syntax.index);
>>>>>>> origin/master
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
<<<<<<< HEAD
                               let uu____4537 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4537 in
=======
                               let uu____4518 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4518 in
>>>>>>> origin/master
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
<<<<<<< HEAD
                  | uu____4639 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4643 = tc_binders env1 bs in
                  match uu____4643 with
                  | (bs1,envbody,g,uu____4664) ->
                      let uu____4665 =
                        let uu____4672 =
                          let uu____4673 = FStar_Syntax_Subst.compress body1 in
                          uu____4673.FStar_Syntax_Syntax.n in
                        match uu____4672 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4685) ->
                            let uu____4721 = tc_comp envbody c in
                            (match uu____4721 with
                             | (c1,uu____4732,g') ->
                                 let uu____4734 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4736 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), uu____4734, body1, uu____4736))
                        | uu____4739 -> (None, None, body1, g) in
                      (match uu____4665 with
=======
                  | uu____4620 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4624 = tc_binders env1 bs in
                  match uu____4624 with
                  | (bs1,envbody,g,uu____4645) ->
                      let uu____4646 =
                        let uu____4653 =
                          let uu____4654 = FStar_Syntax_Subst.compress body1 in
                          uu____4654.FStar_Syntax_Syntax.n in
                        match uu____4653 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4666) ->
                            let uu____4702 = tc_comp envbody c in
                            (match uu____4702 with
                             | (c1,uu____4713,g') ->
                                 let uu____4715 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4717 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), uu____4715, body1, uu____4717))
                        | uu____4720 -> (None, None, body1, g) in
                      (match uu____4646 with
>>>>>>> origin/master
                       | (copt,tacopt,body2,g1) ->
                           (None, bs1, [], copt, tacopt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
<<<<<<< HEAD
                  let uu____4798 =
                    let uu____4799 = FStar_Syntax_Subst.compress t2 in
                    uu____4799.FStar_Syntax_Syntax.n in
                  match uu____4798 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____4816 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4830 -> failwith "Impossible");
                       (let uu____4834 = tc_binders env1 bs in
                        match uu____4834 with
                        | (bs1,envbody,g,uu____4856) ->
                            let uu____4857 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4857 with
                             | (envbody1,uu____4876) ->
=======
                  let uu____4779 =
                    let uu____4780 = FStar_Syntax_Subst.compress t2 in
                    uu____4780.FStar_Syntax_Syntax.n in
                  match uu____4779 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____4797 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4809 -> failwith "Impossible");
                       (let uu____4813 = tc_binders env1 bs in
                        match uu____4813 with
                        | (bs1,envbody,g,uu____4835) ->
                            let uu____4836 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4836 with
                             | (envbody1,uu____4855) ->
>>>>>>> origin/master
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
<<<<<<< HEAD
                           uu____4887;
                         FStar_Syntax_Syntax.tk = uu____4888;
                         FStar_Syntax_Syntax.pos = uu____4889;
                         FStar_Syntax_Syntax.vars = uu____4890;_},uu____4891)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4919 -> failwith "Impossible");
                       (let uu____4923 = tc_binders env1 bs in
                        match uu____4923 with
                        | (bs1,envbody,g,uu____4945) ->
                            let uu____4946 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4946 with
                             | (envbody1,uu____4965) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4977) ->
                      let uu____4982 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____4982 with
                       | (uu____5011,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____5051 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____5051 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5114 c_expected2 =
                               match uu____5114 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____5175 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____5175)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____5192 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5192 in
                                        let uu____5193 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____5193)
=======
                           uu____4866;
                         FStar_Syntax_Syntax.tk = uu____4867;
                         FStar_Syntax_Syntax.pos = uu____4868;
                         FStar_Syntax_Syntax.vars = uu____4869;_},uu____4870)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4896 -> failwith "Impossible");
                       (let uu____4900 = tc_binders env1 bs in
                        match uu____4900 with
                        | (bs1,envbody,g,uu____4922) ->
                            let uu____4923 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4923 with
                             | (envbody1,uu____4942) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4954) ->
                      let uu____4959 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____4959 with
                       | (uu____4988,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____5028 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____5028 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5091 c_expected2 =
                               match uu____5091 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____5152 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____5152)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____5169 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5169 in
                                        let uu____5170 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____5170)
>>>>>>> origin/master
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
<<<<<<< HEAD
                                               let uu____5234 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____5234 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5246 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____5246 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5273 =
                                                           let uu____5289 =
=======
                                               let uu____5211 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____5211 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5223 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____5223 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5250 =
                                                           let uu____5266 =
>>>>>>> origin/master
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
<<<<<<< HEAD
                                                             uu____5289,
                                                             subst2) in
                                                         handle_more
                                                           uu____5273
                                                           c_expected4))
                                           | uu____5298 ->
                                               let uu____5299 =
                                                 let uu____5300 =
=======
                                                             uu____5266,
                                                             subst2) in
                                                         handle_more
                                                           uu____5250
                                                           c_expected4))
                                           | uu____5275 ->
                                               let uu____5276 =
                                                 let uu____5277 =
>>>>>>> origin/master
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
<<<<<<< HEAD
                                                   uu____5300 in
                                               fail uu____5299 t3)
=======
                                                   uu____5277 in
                                               fail uu____5276 t3)
>>>>>>> origin/master
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
<<<<<<< HEAD
                             let uu____5316 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5316 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___107_5354 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___107_5354.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___107_5354.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___107_5354.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___107_5354.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___107_5354.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___107_5354.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___107_5354.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___107_5354.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___107_5354.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___107_5354.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___107_5354.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___107_5354.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___107_5354.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___107_5354.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___107_5354.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___107_5354.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___107_5354.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___107_5354.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___107_5354.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___107_5354.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___107_5354.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___107_5354.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___107_5354.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5368  ->
                                     fun uu____5369  ->
                                       match (uu____5368, uu____5369) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5394 =
                                             let uu____5398 =
                                               let uu____5399 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5399
                                                 FStar_Pervasives.fst in
                                             tc_term uu____5398 t3 in
                                           (match uu____5394 with
                                            | (t4,uu____5411,uu____5412) ->
=======
                             let uu____5293 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5293 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___107_5331 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___107_5331.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___107_5331.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___107_5331.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___107_5331.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___107_5331.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___107_5331.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___107_5331.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___107_5331.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___107_5331.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___107_5331.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___107_5331.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___107_5331.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___107_5331.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___107_5331.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___107_5331.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___107_5331.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___107_5331.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___107_5331.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___107_5331.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___107_5331.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___107_5331.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___107_5331.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___107_5331.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5345  ->
                                     fun uu____5346  ->
                                       match (uu____5345, uu____5346) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5371 =
                                             let uu____5375 =
                                               let uu____5376 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5376
                                                 FStar_Pervasives.fst in
                                             tc_term uu____5375 t3 in
                                           (match uu____5371 with
                                            | (t4,uu____5388,uu____5389) ->
>>>>>>> origin/master
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
<<<<<<< HEAD
                                                      let uu____5419 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___108_5420
=======
                                                      let uu____5396 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___108_5397
>>>>>>> origin/master
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
<<<<<<< HEAD
                                                               (uu___108_5420.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___108_5420.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5419 ::
                                                        letrec_binders
                                                  | uu____5421 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5424 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5424 with
                            | (envbody,bs1,g,c) ->
                                let uu____5456 =
                                  let uu____5460 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5460
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5456 with
=======
                                                               (uu___108_5397.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___108_5397.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5396 ::
                                                        letrec_binders
                                                  | uu____5398 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5401 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5401 with
                            | (envbody,bs1,g,c) ->
                                let uu____5433 =
                                  let uu____5437 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5437
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5433 with
>>>>>>> origin/master
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), None, envbody2, body1, g))))
<<<<<<< HEAD
                  | uu____5496 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5511 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5511
                      else
                        (let uu____5513 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5513 with
                         | (uu____5541,bs1,uu____5543,c_opt,tacopt,envbody,body2,g)
=======
                  | uu____5473 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5488 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5488
                      else
                        (let uu____5490 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5490 with
                         | (uu____5518,bs1,uu____5520,c_opt,tacopt,envbody,body2,g)
>>>>>>> origin/master
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, tacopt,
                               envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
<<<<<<< HEAD
          let uu____5568 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5568 with
          | (env1,topt) ->
              ((let uu____5580 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5580
                then
                  let uu____5581 =
=======
          let uu____5545 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5545 with
          | (env1,topt) ->
              ((let uu____5557 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5557
                then
                  let uu____5558 =
>>>>>>> origin/master
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
<<<<<<< HEAD
                    uu____5581
=======
                    uu____5558
>>>>>>> origin/master
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
<<<<<<< HEAD
               (let uu____5585 = expected_function_typ1 env1 topt body in
                match uu____5585 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5620 =
                      tc_term
                        (let uu___109_5624 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___109_5624.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___109_5624.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___109_5624.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___109_5624.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___109_5624.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___109_5624.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___109_5624.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___109_5624.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___109_5624.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___109_5624.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___109_5624.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___109_5624.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___109_5624.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___109_5624.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___109_5624.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___109_5624.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___109_5624.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___109_5624.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___109_5624.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___109_5624.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___109_5624.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___109_5624.FStar_TypeChecker_Env.qname_and_index)
                         }) body1 in
                    (match uu____5620 with
=======
               (let uu____5562 = expected_function_typ1 env1 topt body in
                match uu____5562 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5597 =
                      tc_term
                        (let uu___109_5601 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___109_5601.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___109_5601.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___109_5601.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___109_5601.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___109_5601.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___109_5601.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___109_5601.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___109_5601.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___109_5601.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___109_5601.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___109_5601.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___109_5601.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___109_5601.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___109_5601.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___109_5601.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___109_5601.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___109_5601.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___109_5601.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___109_5601.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___109_5601.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___109_5601.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___109_5601.FStar_TypeChecker_Env.qname_and_index)
                         }) body1 in
                    (match uu____5597 with
>>>>>>> origin/master
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
<<<<<<< HEAD
                         ((let uu____5633 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5633
                           then
                             let uu____5634 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5643 =
                               let uu____5644 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5644 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5634 uu____5643
                           else ());
                          (let uu____5646 =
                             let uu____5650 =
                               let uu____5653 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5653) in
                             check_expected_effect
                               (let uu___110_5658 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___110_5658.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___110_5658.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___110_5658.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___110_5658.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___110_5658.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___110_5658.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___110_5658.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___110_5658.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___110_5658.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___110_5658.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___110_5658.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___110_5658.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___110_5658.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___110_5658.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___110_5658.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___110_5658.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___110_5658.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___110_5658.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___110_5658.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___110_5658.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___110_5658.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___110_5658.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___110_5658.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5650 in
                           match uu____5646 with
=======
                         ((let uu____5610 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5610
                           then
                             let uu____5611 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5620 =
                               let uu____5621 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5621 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5611 uu____5620
                           else ());
                          (let uu____5623 =
                             let uu____5627 =
                               let uu____5630 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5630) in
                             check_expected_effect
                               (let uu___110_5635 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___110_5635.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___110_5635.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___110_5635.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___110_5635.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___110_5635.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___110_5635.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___110_5635.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___110_5635.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___110_5635.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___110_5635.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___110_5635.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___110_5635.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___110_5635.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___110_5635.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___110_5635.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___110_5635.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___110_5635.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___110_5635.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___110_5635.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___110_5635.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___110_5635.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___110_5635.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___110_5635.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5627 in
                           match uu____5623 with
>>>>>>> origin/master
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
<<<<<<< HEAD
                                 let uu____5667 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5668 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5668) in
                                 if uu____5667
                                 then
                                   let uu____5669 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5669
                                 else
                                   (let guard2 =
                                      let uu____5672 =
=======
                                 let uu____5644 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5645 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5645) in
                                 if uu____5644
                                 then
                                   let uu____5646 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5646
                                 else
                                   (let guard2 =
                                      let uu____5649 =
>>>>>>> origin/master
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
<<<<<<< HEAD
                                        uu____5672 in
=======
                                        uu____5649 in
>>>>>>> origin/master
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
<<<<<<< HEAD
                                 let uu____5679 =
                                   let uu____5686 =
                                     let uu____5692 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     FStar_All.pipe_right uu____5692
                                       (fun _0_30  -> FStar_Util.Inl _0_30) in
                                   Some uu____5686 in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5679 in
                               let uu____5706 =
=======
                                 let uu____5656 =
                                   let uu____5663 =
                                     let uu____5669 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     FStar_All.pipe_right uu____5669
                                       (fun _0_30  -> FStar_Util.Inl _0_30) in
                                   Some uu____5663 in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5656 in
                               let uu____5683 =
>>>>>>> origin/master
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
<<<<<<< HEAD
                                          uu____5721 -> (e, t1, guard2)
                                      | uu____5729 ->
                                          let uu____5730 =
                                            if use_teq
                                            then
                                              let uu____5735 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5735)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5730 with
                                           | (e1,guard') ->
                                               let uu____5742 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5742)))
                                 | None  -> (e, tfun_computed, guard2) in
                               (match uu____5706 with
=======
                                          uu____5698 -> (e, t1, guard2)
                                      | uu____5706 ->
                                          let uu____5707 =
                                            if use_teq
                                            then
                                              let uu____5712 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5712)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5707 with
                                           | (e1,guard') ->
                                               let uu____5719 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5719)))
                                 | None  -> (e, tfun_computed, guard2) in
                               (match uu____5683 with
>>>>>>> origin/master
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
<<<<<<< HEAD
                                    let uu____5755 =
=======
                                    let uu____5732 =
>>>>>>> origin/master
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
<<<<<<< HEAD
                                    (match uu____5755 with
=======
                                    (match uu____5732 with
>>>>>>> origin/master
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
<<<<<<< HEAD
              (let uu____5791 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____5791
               then
                 let uu____5792 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____5793 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5792
                   uu____5793
               else ());
              (let monadic_application uu____5831 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____5831 with
=======
              (let uu____5768 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____5768
               then
                 let uu____5769 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____5770 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5769
                   uu____5770
               else ());
              (let monadic_application uu____5808 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____5808 with
>>>>>>> origin/master
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
<<<<<<< HEAD
                       let uu___111_5868 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___111_5868.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___111_5868.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___111_5868.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____5869 =
=======
                       let uu___111_5845 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___111_5845.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___111_5845.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___111_5845.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____5846 =
>>>>>>> origin/master
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
<<<<<<< HEAD
                       | uu____5878 ->
                           let g =
                             let uu____5883 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____5883
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____5884 =
                             let uu____5885 =
                               let uu____5888 =
                                 let uu____5889 =
                                   let uu____5890 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____5890 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5889 in
                               FStar_Syntax_Syntax.mk_Total uu____5888 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5885 in
                           (uu____5884, g) in
                     (match uu____5869 with
                      | (cres2,guard1) ->
                          ((let uu____5901 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____5901
                            then
                              let uu____5902 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5902
                            else ());
                           (let cres3 =
                              let uu____5905 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____5905
=======
                       | uu____5855 ->
                           let g =
                             let uu____5860 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____5860
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____5861 =
                             let uu____5862 =
                               let uu____5865 =
                                 let uu____5866 =
                                   let uu____5867 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____5867 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5866 in
                               FStar_Syntax_Syntax.mk_Total uu____5865 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5862 in
                           (uu____5861, g) in
                     (match uu____5846 with
                      | (cres2,guard1) ->
                          ((let uu____5878 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____5878
                            then
                              let uu____5879 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5879
                            else ());
                           (let cres3 =
                              let uu____5882 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____5882
>>>>>>> origin/master
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
<<<<<<< HEAD
                                   fun uu____5928  ->
                                     match uu____5928 with
                                     | ((e,q),x,c) ->
                                         let uu____5951 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____5951
=======
                                   fun uu____5905  ->
                                     match uu____5905 with
                                     | ((e,q),x,c) ->
                                         let uu____5928 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____5928
>>>>>>> origin/master
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
<<<<<<< HEAD
                              let uu____5960 =
                                let uu____5961 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____5961.FStar_Syntax_Syntax.n in
                              match uu____5960 with
=======
                              let uu____5937 =
                                let uu____5938 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____5938.FStar_Syntax_Syntax.n in
                              match uu____5937 with
>>>>>>> origin/master
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
<<<<<<< HEAD
                              | uu____5965 -> false in
=======
                              | uu____5942 -> false in
>>>>>>> origin/master
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
<<<<<<< HEAD
                                       fun uu____5975  ->
                                         match uu____5975 with
                                         | (arg,uu____5983,uu____5984) -> arg
=======
                                       fun uu____5952  ->
                                         match uu____5952 with
                                         | (arg,uu____5960,uu____5961) -> arg
>>>>>>> origin/master
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
<<<<<<< HEAD
                                (let uu____5996 =
                                   let map_fun uu____6031 =
                                     match uu____6031 with
                                     | ((e,q),uu____6051,c) ->
                                         let uu____6057 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6057
=======
                                (let uu____5973 =
                                   let map_fun uu____6008 =
                                     match uu____6008 with
                                     | ((e,q),uu____6028,c) ->
                                         let uu____6034 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6034
>>>>>>> origin/master
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
<<<<<<< HEAD
                                            let uu____6087 =
                                              let uu____6090 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____6090, q) in
=======
                                            let uu____6064 =
                                              let uu____6067 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____6067, q) in
>>>>>>> origin/master
                                            ((Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
<<<<<<< HEAD
                                                  e1)), uu____6087)) in
                                   let uu____6108 =
                                     let uu____6122 =
                                       let uu____6135 =
                                         let uu____6143 =
                                           let uu____6148 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____6148, None, chead1) in
                                         uu____6143 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____6135 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6122 in
                                   match uu____6108 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6243 =
                                         let uu____6244 =
                                           FStar_List.hd reverse_args in
                                         fst uu____6244 in
                                       let uu____6249 =
                                         let uu____6253 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6253 in
                                       (lifted_args, uu____6243, uu____6249) in
                                 match uu____5996 with
=======
                                                  e1)), uu____6064)) in
                                   let uu____6085 =
                                     let uu____6099 =
                                       let uu____6112 =
                                         let uu____6120 =
                                           let uu____6125 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____6125, None, chead1) in
                                         uu____6120 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____6112 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6099 in
                                   match uu____6085 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6220 =
                                         let uu____6221 =
                                           FStar_List.hd reverse_args in
                                         fst uu____6221 in
                                       let uu____6226 =
                                         let uu____6230 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6230 in
                                       (lifted_args, uu____6220, uu____6226) in
                                 match uu____5973 with
>>>>>>> origin/master
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
<<<<<<< HEAD
                                     let bind_lifted_args e uu___86_6321 =
                                       match uu___86_6321 with
=======
                                     let bind_lifted_args e uu___86_6298 =
                                       match uu___86_6298 with
>>>>>>> origin/master
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
<<<<<<< HEAD
                                             let uu____6363 =
                                               let uu____6366 =
                                                 let uu____6367 =
                                                   let uu____6375 =
                                                     let uu____6376 =
                                                       let uu____6377 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6377] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6376 e in
                                                   ((false, [lb]),
                                                     uu____6375) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6367 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6366 in
                                             uu____6363 None
=======
                                             let uu____6340 =
                                               let uu____6343 =
                                                 let uu____6344 =
                                                   let uu____6352 =
                                                     let uu____6353 =
                                                       let uu____6354 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6354] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6353 e in
                                                   ((false, [lb]),
                                                     uu____6352) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6344 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6343 in
                                             uu____6340 None
>>>>>>> origin/master
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
<<<<<<< HEAD
                            let uu____6411 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6411 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6465 bs args1 =
                 match uu____6465 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6548))::rest,
                         (uu____6550,None )::uu____6551) ->
=======
                            let uu____6388 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6388 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6442 bs args1 =
                 match uu____6442 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6525))::rest,
                         (uu____6527,None )::uu____6528) ->
>>>>>>> origin/master
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 = check_no_escape (Some head1) env fvs t in
<<<<<<< HEAD
                          let uu____6588 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6588 with
                           | (varg,uu____6599,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6612 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6612) in
                               let uu____6613 =
                                 let uu____6631 =
                                   let uu____6639 =
                                     let uu____6646 =
                                       let uu____6647 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____6647
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, None, uu____6646) in
                                   uu____6639 :: outargs in
                                 let uu____6657 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____6631, (arg :: arg_rets),
                                   uu____6657, fvs) in
                               tc_args head_info uu____6613 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit
                               uu____6717),Some (FStar_Syntax_Syntax.Implicit
                               uu____6718)) -> ()
                            | (None ,None ) -> ()
                            | (Some (FStar_Syntax_Syntax.Equality ),None ) ->
                                ()
                            | uu____6725 ->
=======
                          let uu____6565 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6565 with
                           | (varg,uu____6576,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6589 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6589) in
                               let uu____6590 =
                                 let uu____6608 =
                                   let uu____6616 =
                                     let uu____6623 =
                                       let uu____6624 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____6624
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, None, uu____6623) in
                                   uu____6616 :: outargs in
                                 let uu____6634 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____6608, (arg :: arg_rets),
                                   uu____6634, fvs) in
                               tc_args head_info uu____6590 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit
                               uu____6694),Some (FStar_Syntax_Syntax.Implicit
                               uu____6695)) -> ()
                            | (None ,None ) -> ()
                            | (Some (FStar_Syntax_Syntax.Equality ),None ) ->
                                ()
                            | uu____6702 ->
>>>>>>> origin/master
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
<<<<<<< HEAD
                              let uu___112_6732 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___112_6732.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___112_6732.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6734 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6734
                             then
                               let uu____6735 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6735
=======
                              let uu___112_6709 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___112_6709.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___112_6709.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6711 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6711
                             then
                               let uu____6712 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6712
>>>>>>> origin/master
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
<<<<<<< HEAD
                               let uu___113_6740 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___113_6740.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___113_6740.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___113_6740.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___113_6740.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___113_6740.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___113_6740.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___113_6740.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___113_6740.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___113_6740.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___113_6740.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___113_6740.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___113_6740.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___113_6740.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___113_6740.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___113_6740.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___113_6740.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___113_6740.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___113_6740.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___113_6740.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___113_6740.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___113_6740.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___113_6740.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___113_6740.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             (let uu____6742 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6742
                              then
                                let uu____6743 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6744 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6745 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6743 uu____6744 uu____6745
                              else ());
                             (let uu____6747 = tc_term env2 e in
                              match uu____6747 with
=======
                               let uu___113_6717 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___113_6717.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___113_6717.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___113_6717.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___113_6717.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___113_6717.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___113_6717.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___113_6717.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___113_6717.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___113_6717.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___113_6717.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___113_6717.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___113_6717.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___113_6717.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___113_6717.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___113_6717.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___113_6717.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___113_6717.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___113_6717.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___113_6717.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___113_6717.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___113_6717.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___113_6717.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___113_6717.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             (let uu____6719 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6719
                              then
                                let uu____6720 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6721 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6722 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6720 uu____6721 uu____6722
                              else ());
                             (let uu____6724 = tc_term env2 e in
                              match uu____6724 with
>>>>>>> origin/master
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
<<<<<<< HEAD
                                    let uu____6764 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____6764 in
                                  let uu____6765 =
=======
                                    let uu____6741 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____6741 in
                                  let uu____6742 =
>>>>>>> origin/master
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
<<<<<<< HEAD
                                  if uu____6765
                                  then
                                    let subst2 =
                                      let uu____6770 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6770 e1 in
=======
                                  if uu____6742
                                  then
                                    let subst2 =
                                      let uu____6747 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6747 e1 in
>>>>>>> origin/master
                                    tc_args head_info
                                      (subst2, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        (x1 :: fvs)) rest rest'))))
<<<<<<< HEAD
                      | (uu____6818,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6839) ->
                          let uu____6869 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____6869 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6892 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____6892
=======
                      | (uu____6795,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6816) ->
                          let uu____6846 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____6846 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6869 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____6869
>>>>>>> origin/master
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
<<<<<<< HEAD
                                     let uu____6908 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____6908 with
=======
                                     let uu____6885 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____6885 with
>>>>>>> origin/master
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
<<<<<<< HEAD
                                          ((let uu____6922 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____6922
                                            then
                                              let uu____6923 =
=======
                                          ((let uu____6899 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____6899
                                            then
                                              let uu____6900 =
>>>>>>> origin/master
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
<<<<<<< HEAD
                                                uu____6923
=======
                                                uu____6900
>>>>>>> origin/master
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
<<<<<<< HEAD
                                 | uu____6945 when Prims.op_Negation norm1 ->
                                     let uu____6946 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____6946
                                 | uu____6947 ->
                                     let uu____6948 =
                                       let uu____6949 =
                                         let uu____6952 =
                                           let uu____6953 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____6954 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6953 uu____6954 in
                                         let uu____6958 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____6952, uu____6958) in
                                       FStar_Errors.Error uu____6949 in
                                     raise uu____6948 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____6971 =
                   let uu____6972 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____6972.FStar_Syntax_Syntax.n in
                 match uu____6971 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____6980 ->
=======
                                 | uu____6922 when Prims.op_Negation norm1 ->
                                     let uu____6923 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____6923
                                 | uu____6924 ->
                                     let uu____6925 =
                                       let uu____6926 =
                                         let uu____6929 =
                                           let uu____6930 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____6931 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6930 uu____6931 in
                                         let uu____6935 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____6929, uu____6935) in
                                       FStar_Errors.Error uu____6926 in
                                     raise uu____6925 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____6948 =
                   let uu____6949 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____6949.FStar_Syntax_Syntax.n in
                 match uu____6948 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____6957 ->
>>>>>>> origin/master
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
<<<<<<< HEAD
                           let uu____7046 = tc_term env1 e in
                           (match uu____7046 with
                            | (e1,c,g_e) ->
                                let uu____7059 = tc_args1 env1 tl1 in
                                (match uu____7059 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7081 =
=======
                           let uu____7021 = tc_term env1 e in
                           (match uu____7021 with
                            | (e1,c,g_e) ->
                                let uu____7034 = tc_args1 env1 tl1 in
                                (match uu____7034 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7056 =
>>>>>>> origin/master
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
<<<<<<< HEAD
                                       comps), uu____7081))) in
                     let uu____7092 = tc_args1 env args in
                     (match uu____7092 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7114 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7134  ->
                                      match uu____7134 with
                                      | (uu____7142,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7114 in
                          let ml_or_tot t r1 =
                            let uu____7158 = FStar_Options.ml_ish () in
                            if uu____7158
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7161 =
                              let uu____7164 =
                                let uu____7165 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7165
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7164 in
                            ml_or_tot uu____7161 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7174 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7174
                            then
                              let uu____7175 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7176 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7177 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7175 uu____7176 uu____7177
                            else ());
                           (let uu____7180 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7180);
                           (let comp =
                              let uu____7182 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7187  ->
                                   fun out  ->
                                     match uu____7187 with
=======
                                       comps), uu____7056))) in
                     let uu____7067 = tc_args1 env args in
                     (match uu____7067 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7089 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7109  ->
                                      match uu____7109 with
                                      | (uu____7117,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7089 in
                          let ml_or_tot t r1 =
                            let uu____7133 = FStar_Options.ml_ish () in
                            if uu____7133
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7136 =
                              let uu____7139 =
                                let uu____7140 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7140
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7139 in
                            ml_or_tot uu____7136 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7149 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7149
                            then
                              let uu____7150 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7151 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7152 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7150 uu____7151 uu____7152
                            else ());
                           (let uu____7155 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7155);
                           (let comp =
                              let uu____7157 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7162  ->
                                   fun out  ->
                                     match uu____7162 with
>>>>>>> origin/master
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
<<<<<<< HEAD
                                comps) uu____7182 in
                            let uu____7196 =
=======
                                comps) uu____7157 in
                            let uu____7171 =
>>>>>>> origin/master
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
<<<<<<< HEAD
                            let uu____7203 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7196, comp, uu____7203))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7206;
                        FStar_Syntax_Syntax.tk = uu____7207;
                        FStar_Syntax_Syntax.pos = uu____7208;
                        FStar_Syntax_Syntax.vars = uu____7209;_},uu____7210)
=======
                            let uu____7178 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7171, comp, uu____7178))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7181;
                        FStar_Syntax_Syntax.tk = uu____7182;
                        FStar_Syntax_Syntax.pos = uu____7183;
                        FStar_Syntax_Syntax.vars = uu____7184;_},uu____7185)
>>>>>>> origin/master
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
<<<<<<< HEAD
                           let uu____7290 = tc_term env1 e in
                           (match uu____7290 with
                            | (e1,c,g_e) ->
                                let uu____7303 = tc_args1 env1 tl1 in
                                (match uu____7303 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7325 =
=======
                           let uu____7263 = tc_term env1 e in
                           (match uu____7263 with
                            | (e1,c,g_e) ->
                                let uu____7276 = tc_args1 env1 tl1 in
                                (match uu____7276 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7298 =
>>>>>>> origin/master
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
<<<<<<< HEAD
                                       comps), uu____7325))) in
                     let uu____7336 = tc_args1 env args in
                     (match uu____7336 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7358 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7378  ->
                                      match uu____7378 with
                                      | (uu____7386,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7358 in
                          let ml_or_tot t r1 =
                            let uu____7402 = FStar_Options.ml_ish () in
                            if uu____7402
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7405 =
                              let uu____7408 =
                                let uu____7409 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7409
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7408 in
                            ml_or_tot uu____7405 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7418 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7418
                            then
                              let uu____7419 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7420 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7421 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7419 uu____7420 uu____7421
                            else ());
                           (let uu____7424 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7424);
                           (let comp =
                              let uu____7426 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7431  ->
                                   fun out  ->
                                     match uu____7431 with
=======
                                       comps), uu____7298))) in
                     let uu____7309 = tc_args1 env args in
                     (match uu____7309 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7331 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7351  ->
                                      match uu____7351 with
                                      | (uu____7359,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7331 in
                          let ml_or_tot t r1 =
                            let uu____7375 = FStar_Options.ml_ish () in
                            if uu____7375
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7378 =
                              let uu____7381 =
                                let uu____7382 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7382
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7381 in
                            ml_or_tot uu____7378 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7391 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7391
                            then
                              let uu____7392 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7393 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7394 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7392 uu____7393 uu____7394
                            else ());
                           (let uu____7397 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7397);
                           (let comp =
                              let uu____7399 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7404  ->
                                   fun out  ->
                                     match uu____7404 with
>>>>>>> origin/master
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
<<<<<<< HEAD
                                comps) uu____7426 in
                            let uu____7440 =
=======
                                comps) uu____7399 in
                            let uu____7413 =
>>>>>>> origin/master
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
<<<<<<< HEAD
                            let uu____7447 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7440, comp, uu____7447))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7462 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7462 with
=======
                            let uu____7420 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7413, comp, uu____7420))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7435 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7435 with
>>>>>>> origin/master
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
<<<<<<< HEAD
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7498) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7504,uu____7505)
                     -> check_function_app t
                 | uu____7534 ->
                     let uu____7535 =
                       let uu____7536 =
                         let uu____7539 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7539, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7536 in
                     raise uu____7535 in
=======
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7471) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7477,uu____7478)
                     -> check_function_app t
                 | uu____7507 ->
                     let uu____7508 =
                       let uu____7509 =
                         let uu____7512 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7512, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7509 in
                     raise uu____7508 in
>>>>>>> origin/master
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
<<<<<<< HEAD
                  let uu____7590 =
                    FStar_List.fold_left2
                      (fun uu____7603  ->
                         fun uu____7604  ->
                           fun uu____7605  ->
                             match (uu____7603, uu____7604, uu____7605) with
=======
                  let uu____7563 =
                    FStar_List.fold_left2
                      (fun uu____7576  ->
                         fun uu____7577  ->
                           fun uu____7578  ->
                             match (uu____7576, uu____7577, uu____7578) with
>>>>>>> origin/master
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
<<<<<<< HEAD
                                  (let uu____7649 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7649 with
=======
                                  (let uu____7622 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7622 with
>>>>>>> origin/master
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
<<<<<<< HEAD
                                         let uu____7661 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7661 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7663 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7663) &&
                                              (let uu____7664 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7664)) in
                                       let uu____7665 =
                                         let uu____7671 =
                                           let uu____7677 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7677] in
                                         FStar_List.append seen uu____7671 in
                                       let uu____7682 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7665, uu____7682, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7590 with
=======
                                         let uu____7634 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7634 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7636 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7636) &&
                                              (let uu____7637 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7637)) in
                                       let uu____7638 =
                                         let uu____7644 =
                                           let uu____7650 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7650] in
                                         FStar_List.append seen uu____7644 in
                                       let uu____7655 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7638, uu____7655, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7563 with
>>>>>>> origin/master
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
<<<<<<< HEAD
                           let uu____7711 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7711
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7713 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7713 with | (c2,g) -> (e, c2, g)))
              | uu____7725 ->
=======
                           let uu____7684 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7684
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7686 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7686 with | (c2,g) -> (e, c2, g)))
              | uu____7698 ->
>>>>>>> origin/master
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
<<<<<<< HEAD
        let uu____7747 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7747 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7773 = branch1 in
            (match uu____7773 with
             | (cpat,uu____7793,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7831 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____7831 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____7848 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____7848
                         then
                           let uu____7849 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____7850 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7849 uu____7850
=======
        let uu____7720 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7720 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7746 = branch1 in
            (match uu____7746 with
             | (cpat,uu____7766,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7804 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____7804 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____7821 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____7821
                         then
                           let uu____7822 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____7823 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7822 uu____7823
>>>>>>> origin/master
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
<<<<<<< HEAD
                         let uu____7853 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____7853 with
                         | (env1,uu____7864) ->
                             let env11 =
                               let uu___114_7868 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___114_7868.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___114_7868.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___114_7868.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___114_7868.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___114_7868.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___114_7868.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___114_7868.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___114_7868.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___114_7868.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___114_7868.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___114_7868.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___114_7868.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___114_7868.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___114_7868.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___114_7868.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___114_7868.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___114_7868.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___114_7868.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___114_7868.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___114_7868.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___114_7868.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___114_7868.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___114_7868.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____7871 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____7871
                               then
                                 let uu____7872 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____7873 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____7872 uu____7873
                               else ());
                              (let uu____7875 = tc_tot_or_gtot_term env11 exp in
                               match uu____7875 with
=======
                         let uu____7826 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____7826 with
                         | (env1,uu____7837) ->
                             let env11 =
                               let uu___114_7841 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___114_7841.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___114_7841.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___114_7841.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___114_7841.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___114_7841.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___114_7841.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___114_7841.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___114_7841.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___114_7841.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___114_7841.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___114_7841.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___114_7841.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___114_7841.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___114_7841.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___114_7841.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___114_7841.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___114_7841.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___114_7841.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___114_7841.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___114_7841.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___114_7841.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___114_7841.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___114_7841.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____7844 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____7844
                               then
                                 let uu____7845 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____7846 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____7845 uu____7846
                               else ());
                              (let uu____7848 = tc_tot_or_gtot_term env11 exp in
                               match uu____7848 with
>>>>>>> origin/master
                               | (exp1,lc,g) ->
                                   let g' =
                                     FStar_TypeChecker_Rel.teq env11
                                       lc.FStar_Syntax_Syntax.res_typ
                                       expected_pat_t in
                                   let g1 =
                                     FStar_TypeChecker_Rel.conj_guard g g' in
<<<<<<< HEAD
                                   let uu____7890 =
=======
                                   let uu____7863 =
>>>>>>> origin/master
                                     let env12 =
                                       FStar_TypeChecker_Env.set_range env11
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let g2 =
<<<<<<< HEAD
                                       let uu___115_7893 = g1 in
=======
                                       let uu___115_7866 = g1 in
>>>>>>> origin/master
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
<<<<<<< HEAD
                                           (uu___115_7893.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___115_7893.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___115_7893.FStar_TypeChecker_Env.implicits)
                                       } in
                                     let uu____7894 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env12 g2 in
                                     FStar_All.pipe_right uu____7894
=======
                                           (uu___115_7866.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___115_7866.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___115_7866.FStar_TypeChecker_Env.implicits)
                                       } in
                                     let uu____7867 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env12 g2 in
                                     FStar_All.pipe_right uu____7867
>>>>>>> origin/master
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env11 exp1 in
<<<<<<< HEAD
                                   let uvars_to_string uvs =
                                     let uu____7906 =
                                       let uu____7908 =
                                         FStar_All.pipe_right uvs
                                           FStar_Util.set_elements in
                                       FStar_All.pipe_right uu____7908
                                         (FStar_List.map
                                            (fun uu____7926  ->
                                               match uu____7926 with
                                               | (u,uu____7930) ->
                                                   FStar_Syntax_Print.uvar_to_string
                                                     u)) in
                                     FStar_All.pipe_right uu____7906
                                       (FStar_String.concat ", ") in
=======
>>>>>>> origin/master
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
<<<<<<< HEAD
                                   ((let uu____7941 =
                                       let uu____7942 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____7942 in
                                     if uu____7941
                                     then
                                       let unresolved =
                                         let uu____7949 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____7949
                                           FStar_Util.set_elements in
                                       let uu____7963 =
                                         let uu____7964 =
                                           let uu____7967 =
                                             let uu____7968 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____7969 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____7970 =
                                               let uu____7971 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____7979  ->
                                                         match uu____7979
                                                         with
                                                         | (u,uu____7983) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____7971
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____7968 uu____7969
                                               uu____7970 in
                                           (uu____7967,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____7964 in
                                       raise uu____7963
                                     else ());
                                    (let uu____7987 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____7987
                                     then
                                       let uu____7988 =
=======
                                   ((let uu____7878 =
                                       let uu____7879 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____7879 in
                                     if uu____7878
                                     then
                                       let unresolved =
                                         let uu____7886 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____7886
                                           FStar_Util.set_elements in
                                       let uu____7900 =
                                         let uu____7901 =
                                           let uu____7904 =
                                             let uu____7905 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____7906 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____7907 =
                                               let uu____7908 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____7920  ->
                                                         match uu____7920
                                                         with
                                                         | (u,uu____7928) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____7908
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____7905 uu____7906
                                               uu____7907 in
                                           (uu____7904,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____7901 in
                                       raise uu____7900
                                     else ());
                                    (let uu____7943 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____7943
                                     then
                                       let uu____7944 =
>>>>>>> origin/master
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
<<<<<<< HEAD
                                         uu____7988
=======
                                         uu____7944
>>>>>>> origin/master
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
<<<<<<< HEAD
                 let uu____7996 =
                   let uu____8000 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____8000
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____7996 with
                  | (scrutinee_env,uu____8013) ->
                      let uu____8016 = tc_pat true pat_t pattern in
                      (match uu____8016 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____8038 =
=======
                 let uu____7952 =
                   let uu____7956 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____7956
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____7952 with
                  | (scrutinee_env,uu____7969) ->
                      let uu____7972 = tc_pat true pat_t pattern in
                      (match uu____7972 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____7994 =
>>>>>>> origin/master
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
<<<<<<< HEAD
                                 let uu____8053 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____8053
=======
                                 let uu____8009 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____8009
>>>>>>> origin/master
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
<<<<<<< HEAD
                                   (let uu____8061 =
                                      let uu____8065 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____8065 e in
                                    match uu____8061 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____8038 with
                            | (when_clause1,g_when) ->
                                let uu____8085 = tc_term pat_env branch_exp in
                                (match uu____8085 with
=======
                                   (let uu____8017 =
                                      let uu____8021 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____8021 e in
                                    match uu____8017 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____7994 with
                            | (when_clause1,g_when) ->
                                let uu____8041 = tc_term pat_env branch_exp in
                                (match uu____8041 with
>>>>>>> origin/master
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
<<<<<<< HEAD
                                           let uu____8104 =
=======
                                           let uu____8060 =
>>>>>>> origin/master
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_31  -> Some _0_31)
<<<<<<< HEAD
                                             uu____8104 in
                                     let uu____8106 =
                                       let eqs =
                                         let uu____8112 =
                                           let uu____8113 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____8113 in
                                         if uu____8112
=======
                                             uu____8060 in
                                     let uu____8062 =
                                       let eqs =
                                         let uu____8068 =
                                           let uu____8069 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____8069 in
                                         if uu____8068
>>>>>>> origin/master
                                         then None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
<<<<<<< HEAD
                                                uu____8118 -> None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8129 -> None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8130 -> None
                                            | uu____8131 ->
                                                let uu____8132 =
                                                  let uu____8133 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8133 pat_t
                                                    scrutinee_tm e in
                                                Some uu____8132) in
                                       let uu____8134 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____8134 with
                                       | (c1,g_branch1) ->
                                           let uu____8144 =
                                             match (eqs, when_condition) with
                                             | uu____8151 when
                                                 let uu____8156 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8156
=======
                                                uu____8074 -> None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8083 -> None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8084 -> None
                                            | uu____8085 ->
                                                let uu____8086 =
                                                  let uu____8087 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8087 pat_t
                                                    scrutinee_tm e in
                                                Some uu____8086) in
                                       let uu____8088 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____8088 with
                                       | (c1,g_branch1) ->
                                           let uu____8098 =
                                             match (eqs, when_condition) with
                                             | uu____8105 when
                                                 let uu____8110 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8110
>>>>>>> origin/master
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
<<<<<<< HEAD
                                                 let uu____8164 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8165 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8164, uu____8165)
=======
                                                 let uu____8118 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8119 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8118, uu____8119)
>>>>>>> origin/master
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
<<<<<<< HEAD
                                                   let uu____8172 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8172 in
                                                 let uu____8173 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8174 =
                                                   let uu____8175 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8175 g_when in
                                                 (uu____8173, uu____8174)
=======
                                                   let uu____8126 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8126 in
                                                 let uu____8127 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8128 =
                                                   let uu____8129 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8129 g_when in
                                                 (uu____8127, uu____8128)
>>>>>>> origin/master
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
<<<<<<< HEAD
                                                 let uu____8181 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8181, g_when) in
                                           (match uu____8144 with
=======
                                                 let uu____8135 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8135, g_when) in
                                           (match uu____8098 with
>>>>>>> origin/master
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
<<<<<<< HEAD
                                                let uu____8189 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____8190 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8189, uu____8190,
                                                  g_branch1)) in
                                     (match uu____8106 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8203 =
                                              let uu____8204 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8204 in
                                            if uu____8203
=======
                                                let uu____8143 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____8144 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8143, uu____8144,
                                                  g_branch1)) in
                                     (match uu____8062 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8157 =
                                              let uu____8158 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8158 in
                                            if uu____8157
>>>>>>> origin/master
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
<<<<<<< HEAD
                                                   let uu____8235 =
                                                     let uu____8236 =
                                                       let uu____8237 =
                                                         let uu____8239 =
                                                           let uu____8243 =
=======
                                                   let uu____8189 =
                                                     let uu____8190 =
                                                       let uu____8191 =
                                                         let uu____8193 =
                                                           let uu____8197 =
>>>>>>> origin/master
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
<<<<<<< HEAD
                                                             env uu____8243 in
                                                         snd uu____8239 in
                                                       FStar_List.length
                                                         uu____8237 in
                                                     uu____8236 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8235
=======
                                                             env uu____8197 in
                                                         snd uu____8193 in
                                                       FStar_List.length
                                                         uu____8191 in
                                                     uu____8190 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8189
>>>>>>> origin/master
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
<<<<<<< HEAD
                                                     let uu____8252 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8252 with
                                                     | None  -> []
                                                     | uu____8263 ->
=======
                                                     let uu____8206 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8206 with
                                                     | None  -> []
                                                     | uu____8217 ->
>>>>>>> origin/master
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None in
                                                         let disc1 =
<<<<<<< HEAD
                                                           let uu____8273 =
                                                             let uu____8274 =
                                                               let uu____8275
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8275] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8274 in
                                                           uu____8273 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8280 =
=======
                                                           let uu____8227 =
                                                             let uu____8228 =
                                                               let uu____8229
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8229] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8228 in
                                                           uu____8227 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8234 =
>>>>>>> origin/master
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool in
<<<<<<< HEAD
                                                         [uu____8280]
                                                   else [] in
                                                 let fail uu____8288 =
                                                   let uu____8289 =
                                                     let uu____8290 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____8291 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____8292 =
=======
                                                         [uu____8234]
                                                   else [] in
                                                 let fail uu____8242 =
                                                   let uu____8243 =
                                                     let uu____8244 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____8245 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____8246 =
>>>>>>> origin/master
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
<<<<<<< HEAD
                                                       uu____8290 uu____8291
                                                       uu____8292 in
                                                   failwith uu____8289 in
=======
                                                       uu____8244 uu____8245
                                                       uu____8246 in
                                                   failwith uu____8243 in
>>>>>>> origin/master
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
<<<<<<< HEAD
                                                       (t1,uu____8313) ->
                                                       head_constructor t1
                                                   | uu____8319 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____8322 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____8322
=======
                                                       (t1,uu____8267) ->
                                                       head_constructor t1
                                                   | uu____8273 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____8276 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____8276
>>>>>>> origin/master
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
<<<<<<< HEAD
                                                     uu____8324 -> []
=======
                                                     uu____8278 -> []
>>>>>>> origin/master
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
<<<<<<< HEAD
                                                          uu____8335;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8336;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8337;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8338;_},uu____8339)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8364 -> []
=======
                                                          uu____8287;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8288;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8289;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8290;_},uu____8291)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8314 -> []
>>>>>>> origin/master
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
<<<<<<< HEAD
                                                     let uu____8366 =
                                                       let uu____8367 =
=======
                                                     let uu____8316 =
                                                       let uu____8317 =
>>>>>>> origin/master
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
<<<<<<< HEAD
                                                         uu____8367
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____8366]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8368 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8378 =
                                                       let uu____8379 =
=======
                                                         uu____8317
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____8316]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8318 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8328 =
                                                       let uu____8329 =
>>>>>>> origin/master
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
<<<<<<< HEAD
                                                         uu____8379 in
                                                     if uu____8378
                                                     then []
                                                     else
                                                       (let uu____8386 =
=======
                                                         uu____8329 in
                                                     if uu____8328
                                                     then []
                                                     else
                                                       (let uu____8336 =
>>>>>>> origin/master
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
<<<<<<< HEAD
                                                          uu____8386)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8392 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8398 =
                                                       let uu____8399 =
=======
                                                          uu____8336)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8342 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8348 =
                                                       let uu____8349 =
>>>>>>> origin/master
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
<<<<<<< HEAD
                                                         uu____8399 in
                                                     if uu____8398
                                                     then []
                                                     else
                                                       (let uu____8406 =
=======
                                                         uu____8349 in
                                                     if uu____8348
                                                     then []
                                                     else
                                                       (let uu____8356 =
>>>>>>> origin/master
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
<<<<<<< HEAD
                                                          uu____8406)
=======
                                                          uu____8356)
>>>>>>> origin/master
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
<<<<<<< HEAD
                                                     let uu____8433 =
                                                       let uu____8434 =
=======
                                                     let uu____8383 =
                                                       let uu____8384 =
>>>>>>> origin/master
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
<<<<<<< HEAD
                                                         uu____8434 in
                                                     if uu____8433
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8443 =
=======
                                                         uu____8384 in
                                                     if uu____8383
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8393 =
>>>>>>> origin/master
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
<<<<<<< HEAD
                                                                    uu____8459
                                                                     ->
                                                                    match uu____8459
                                                                    with
                                                                    | 
                                                                    (ei,uu____8466)
=======
                                                                    uu____8409
                                                                     ->
                                                                    match uu____8409
                                                                    with
                                                                    | 
                                                                    (ei,uu____8416)
>>>>>>> origin/master
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
<<<<<<< HEAD
                                                                    let uu____8476
=======
                                                                    let uu____8426
>>>>>>> origin/master
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
<<<<<<< HEAD
                                                                    (match uu____8476
=======
                                                                    (match uu____8426
>>>>>>> origin/master
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
<<<<<<< HEAD
                                                                    uu____8487
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8496
                                                                    =
                                                                    let uu____8497
=======
                                                                    uu____8437
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8446
                                                                    =
                                                                    let uu____8447
>>>>>>> origin/master
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None in
<<<<<<< HEAD
                                                                    let uu____8502
                                                                    =
                                                                    let uu____8503
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8503] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8497
                                                                    uu____8502 in
                                                                    uu____8496
=======
                                                                    let uu____8452
                                                                    =
                                                                    let uu____8453
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8453] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8447
                                                                    uu____8452 in
                                                                    uu____8446
>>>>>>> origin/master
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
<<<<<<< HEAD
                                                            uu____8443
                                                            FStar_List.flatten in
                                                        let uu____8515 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8515
                                                          sub_term_guards)
                                                 | uu____8519 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8531 =
                                                   let uu____8532 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8532 in
                                                 if uu____8531
=======
                                                            uu____8393
                                                            FStar_List.flatten in
                                                        let uu____8465 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8465
                                                          sub_term_guards)
                                                 | uu____8469 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8481 =
                                                   let uu____8482 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8482 in
                                                 if uu____8481
>>>>>>> origin/master
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
<<<<<<< HEAD
                                                      let uu____8535 =
=======
                                                      let uu____8485 =
>>>>>>> origin/master
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
<<<<<<< HEAD
                                                        uu____8535 in
                                                    let uu____8538 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8538 with
                                                    | (k,uu____8542) ->
                                                        let uu____8543 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8543
                                                         with
                                                         | (t1,uu____8548,uu____8549)
=======
                                                        uu____8485 in
                                                    let uu____8488 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8488 with
                                                    | (k,uu____8492) ->
                                                        let uu____8493 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8493
                                                         with
                                                         | (t1,uu____8498,uu____8499)
>>>>>>> origin/master
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
<<<<<<< HEAD
                                          ((let uu____8555 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8555
                                            then
                                              let uu____8556 =
=======
                                          ((let uu____8505 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8505
                                            then
                                              let uu____8506 =
>>>>>>> origin/master
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
<<<<<<< HEAD
                                                uu____8556
                                            else ());
                                           (let uu____8558 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8558, branch_guard, c1,
=======
                                                uu____8506
                                            else ());
                                           (let uu____8508 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8508, branch_guard, c1,
>>>>>>> origin/master
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
<<<<<<< HEAD
          let uu____8576 = check_let_bound_def true env1 lb in
          (match uu____8576 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8590 =
=======
          let uu____8526 = check_let_bound_def true env1 lb in
          (match uu____8526 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8540 =
>>>>>>> origin/master
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
<<<<<<< HEAD
                   let uu____8599 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____8599, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8602 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8602
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8604 =
                      let uu____8609 =
                        let uu____8615 =
                          let uu____8620 =
                            let uu____8628 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8628) in
                          [uu____8620] in
                        FStar_TypeChecker_Util.generalize env1 uu____8615 in
                      FStar_List.hd uu____8609 in
                    match uu____8604 with
                    | (uu____8657,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8590 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8668 =
                      let uu____8673 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8673
                      then
                        let uu____8678 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8678 with
=======
                   let uu____8549 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____8549, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8552 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8552
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8554 =
                      let uu____8559 =
                        let uu____8565 =
                          let uu____8570 =
                            let uu____8578 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8578) in
                          [uu____8570] in
                        FStar_TypeChecker_Util.generalize env1 uu____8565 in
                      FStar_List.hd uu____8559 in
                    match uu____8554 with
                    | (uu____8607,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8540 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8618 =
                      let uu____8623 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8623
                      then
                        let uu____8628 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8628 with
>>>>>>> origin/master
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
<<<<<<< HEAD
                               ((let uu____8695 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____8695
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8696 =
=======
                               ((let uu____8645 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____8645
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8646 =
>>>>>>> origin/master
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
                                 (uu____8696, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8714 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8714
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8722 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8722
=======
                                 (uu____8646, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8664 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8664
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8672 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8672
>>>>>>> origin/master
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
<<<<<<< HEAD
                    (match uu____8668 with
=======
                    (match uu____8618 with
>>>>>>> origin/master
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
<<<<<<< HEAD
                           let uu____8754 =
=======
                           let uu____8704 =
>>>>>>> origin/master
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
                           (uu____8754,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8773 -> failwith "Impossible"
=======
                           (uu____8704,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8723 -> failwith "Impossible"
>>>>>>> origin/master
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
<<<<<<< HEAD
            let uu___116_8794 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___116_8794.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___116_8794.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___116_8794.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___116_8794.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___116_8794.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___116_8794.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___116_8794.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___116_8794.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___116_8794.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___116_8794.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___116_8794.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___116_8794.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___116_8794.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___116_8794.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___116_8794.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___116_8794.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___116_8794.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___116_8794.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___116_8794.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___116_8794.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___116_8794.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___116_8794.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___116_8794.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____8795 =
            let uu____8801 =
              let uu____8802 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8802 FStar_Pervasives.fst in
            check_let_bound_def false uu____8801 lb in
          (match uu____8795 with
           | (e1,uu____8814,c1,g1,annotated) ->
               let x =
                 let uu___117_8819 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___117_8819.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___117_8819.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8820 =
                 let uu____8823 =
                   let uu____8824 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8824] in
                 FStar_Syntax_Subst.open_term uu____8823 e2 in
               (match uu____8820 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = fst xbinder in
                    let uu____8836 =
                      let uu____8840 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8840 e21 in
                    (match uu____8836 with
=======
            let uu___116_8744 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___116_8744.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___116_8744.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___116_8744.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___116_8744.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___116_8744.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___116_8744.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___116_8744.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___116_8744.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___116_8744.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___116_8744.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___116_8744.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___116_8744.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___116_8744.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___116_8744.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___116_8744.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___116_8744.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___116_8744.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___116_8744.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___116_8744.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___116_8744.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___116_8744.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___116_8744.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___116_8744.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____8745 =
            let uu____8751 =
              let uu____8752 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8752 FStar_Pervasives.fst in
            check_let_bound_def false uu____8751 lb in
          (match uu____8745 with
           | (e1,uu____8764,c1,g1,annotated) ->
               let x =
                 let uu___117_8769 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___117_8769.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___117_8769.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8770 =
                 let uu____8773 =
                   let uu____8774 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8774] in
                 FStar_Syntax_Subst.open_term uu____8773 e2 in
               (match uu____8770 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = fst xbinder in
                    let uu____8786 =
                      let uu____8790 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8790 e21 in
                    (match uu____8786 with
>>>>>>> origin/master
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
<<<<<<< HEAD
                           let uu____8855 =
                             let uu____8858 =
                               let uu____8859 =
                                 let uu____8867 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8867) in
                               FStar_Syntax_Syntax.Tm_let uu____8859 in
                             FStar_Syntax_Syntax.mk uu____8858 in
                           uu____8855
=======
                           let uu____8805 =
                             let uu____8808 =
                               let uu____8809 =
                                 let uu____8817 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8817) in
                               FStar_Syntax_Syntax.Tm_let uu____8809 in
                             FStar_Syntax_Syntax.mk uu____8808 in
                           uu____8805
>>>>>>> origin/master
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
<<<<<<< HEAD
                           let uu____8882 =
                             let uu____8883 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____8884 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____8883
                               c1.FStar_Syntax_Syntax.res_typ uu____8884 e11 in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8882 in
                         let g21 =
                           let uu____8886 =
                             let uu____8887 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____8887 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____8886 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____8889 =
                           let uu____8890 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____8890 in
                         if uu____8889
                         then
                           let tt =
                             let uu____8896 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____8896 FStar_Option.get in
                           ((let uu____8900 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8900
                             then
                               let uu____8901 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____8902 =
=======
                           let uu____8832 =
                             let uu____8833 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____8834 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____8833
                               c1.FStar_Syntax_Syntax.res_typ uu____8834 e11 in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8832 in
                         let g21 =
                           let uu____8836 =
                             let uu____8837 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____8837 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____8836 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____8839 =
                           let uu____8840 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____8840 in
                         if uu____8839
                         then
                           let tt =
                             let uu____8846 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____8846 FStar_Option.get in
                           ((let uu____8850 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8850
                             then
                               let uu____8851 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____8852 =
>>>>>>> origin/master
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
<<<<<<< HEAD
                                 uu____8901 uu____8902
=======
                                 uu____8851 uu____8852
>>>>>>> origin/master
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ in
<<<<<<< HEAD
                            (let uu____8907 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8907
                             then
                               let uu____8908 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____8909 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8908 uu____8909
                             else ());
                            (e4,
                              ((let uu___118_8911 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___118_8911.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___118_8911.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___118_8911.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8912 -> failwith "Impossible"
=======
                            (let uu____8857 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8857
                             then
                               let uu____8858 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____8859 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8858 uu____8859
                             else ());
                            (e4,
                              ((let uu___118_8861 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___118_8861.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___118_8861.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___118_8861.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8862 -> failwith "Impossible"
>>>>>>> origin/master
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
<<<<<<< HEAD
          let uu____8933 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8933 with
           | (lbs1,e21) ->
               let uu____8944 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8944 with
                | (env0,topt) ->
                    let uu____8955 = build_let_rec_env true env0 lbs1 in
                    (match uu____8955 with
                     | (lbs2,rec_env) ->
                         let uu____8966 = check_let_recs rec_env lbs2 in
                         (match uu____8966 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8978 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____8978
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____8982 =
=======
          let uu____8883 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8883 with
           | (lbs1,e21) ->
               let uu____8894 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8894 with
                | (env0,topt) ->
                    let uu____8905 = build_let_rec_env true env0 lbs1 in
                    (match uu____8905 with
                     | (lbs2,rec_env) ->
                         let uu____8916 = check_let_recs rec_env lbs2 in
                         (match uu____8916 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8928 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____8928
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____8932 =
>>>>>>> origin/master
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
<<<<<<< HEAD
                                FStar_All.pipe_right uu____8982
=======
                                FStar_All.pipe_right uu____8932
>>>>>>> origin/master
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
<<<<<<< HEAD
                                     let uu____9007 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____9029 =
=======
                                     let uu____8957 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____8979 =
>>>>>>> origin/master
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
<<<<<<< HEAD
                                                 uu____9029))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____9007 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____9049  ->
                                           match uu____9049 with
=======
                                                 uu____8979))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8957 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____8999  ->
                                           match uu____8999 with
>>>>>>> origin/master
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
<<<<<<< HEAD
                                let uu____9074 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____9074 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____9083 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____9083 with
                                | (lbs5,e22) ->
                                    let uu____9094 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____9109 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env1 g_lbs1 in
                                    (uu____9094, cres, uu____9109)))))))
      | uu____9112 -> failwith "Impossible"
=======
                                let uu____9024 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____9024 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____9033 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____9033 with
                                | (lbs5,e22) ->
                                    ((let uu____9045 =
                                        FStar_TypeChecker_Rel.discharge_guard
                                          env1 g_lbs1 in
                                      FStar_All.pipe_right uu____9045
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1));
                                     (let uu____9046 =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_let
                                              ((true, lbs5), e22)))
                                          (Some
                                             (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos in
                                      (uu____9046, cres,
                                        FStar_TypeChecker_Rel.trivial_guard)))))))))
      | uu____9063 -> failwith "Impossible"
>>>>>>> origin/master
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
<<<<<<< HEAD
          let uu____9133 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9133 with
           | (lbs1,e21) ->
               let uu____9144 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9144 with
                | (env0,topt) ->
                    let uu____9155 = build_let_rec_env false env0 lbs1 in
                    (match uu____9155 with
                     | (lbs2,rec_env) ->
                         let uu____9166 = check_let_recs rec_env lbs2 in
                         (match uu____9166 with
                          | (lbs3,g_lbs) ->
                              let uu____9177 =
=======
          let uu____9084 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9084 with
           | (lbs1,e21) ->
               let uu____9095 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9095 with
                | (env0,topt) ->
                    let uu____9106 = build_let_rec_env false env0 lbs1 in
                    (match uu____9106 with
                     | (lbs2,rec_env) ->
                         let uu____9117 = check_let_recs rec_env lbs2 in
                         (match uu____9117 with
                          | (lbs3,g_lbs) ->
                              let uu____9128 =
>>>>>>> origin/master
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
<<<<<<< HEAD
                                            let uu___119_9188 =
=======
                                            let uu___119_9139 =
>>>>>>> origin/master
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                                (uu___119_9188.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___119_9188.FStar_Syntax_Syntax.index);
=======
                                                (uu___119_9139.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___119_9139.FStar_Syntax_Syntax.index);
>>>>>>> origin/master
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
<<<<<<< HEAD
                                            let uu___120_9190 = lb in
=======
                                            let uu___120_9141 = lb in
>>>>>>> origin/master
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
<<<<<<< HEAD
                                                (uu___120_9190.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___120_9190.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___120_9190.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___120_9190.FStar_Syntax_Syntax.lbdef)
=======
                                                (uu___120_9141.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___120_9141.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___120_9141.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___120_9141.FStar_Syntax_Syntax.lbdef)
>>>>>>> origin/master
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
<<<<<<< HEAD
                              (match uu____9177 with
=======
                              (match uu____9128 with
>>>>>>> origin/master
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
<<<<<<< HEAD
                                   let uu____9207 = tc_term env2 e21 in
                                   (match uu____9207 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9218 =
                                            let uu____9219 =
=======
                                   let uu____9158 = tc_term env2 e21 in
                                   (match uu____9158 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9169 =
                                            let uu____9170 =
>>>>>>> origin/master
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
<<<<<<< HEAD
                                              env2 uu____9219 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9218 in
=======
                                              env2 uu____9170 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9169 in
>>>>>>> origin/master
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
<<<<<<< HEAD
                                          let uu___121_9223 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___121_9223.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___121_9223.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___121_9223.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9224 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9224 with
=======
                                          let uu___121_9174 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___121_9174.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___121_9174.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___121_9174.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9175 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9175 with
>>>>>>> origin/master
                                         | (lbs5,e23) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
<<<<<<< HEAD
                                              | Some uu____9253 ->
=======
                                              | Some uu____9204 ->
>>>>>>> origin/master
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres in
                                                  let cres3 =
<<<<<<< HEAD
                                                    let uu___122_9258 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___122_9258.FStar_Syntax_Syntax.eff_name);
=======
                                                    let uu___122_9209 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___122_9209.FStar_Syntax_Syntax.eff_name);
>>>>>>> origin/master
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
<<<<<<< HEAD
                                                        (uu___122_9258.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___122_9258.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9261 -> failwith "Impossible"
=======
                                                        (uu___122_9209.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___122_9209.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9212 -> failwith "Impossible"
>>>>>>> origin/master
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
<<<<<<< HEAD
          let uu____9284 =
            let uu____9287 =
              let uu____9288 = FStar_Syntax_Subst.compress t in
              uu____9288.FStar_Syntax_Syntax.n in
            let uu____9291 =
              let uu____9292 = FStar_Syntax_Subst.compress lbdef in
              uu____9292.FStar_Syntax_Syntax.n in
            (uu____9287, uu____9291) in
          match uu____9284 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9298,uu____9299)) ->
              let actuals1 =
                let uu____9333 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9333
=======
          let uu____9235 =
            let uu____9238 =
              let uu____9239 = FStar_Syntax_Subst.compress t in
              uu____9239.FStar_Syntax_Syntax.n in
            let uu____9242 =
              let uu____9243 = FStar_Syntax_Subst.compress lbdef in
              uu____9243.FStar_Syntax_Syntax.n in
            (uu____9238, uu____9242) in
          match uu____9235 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9249,uu____9250)) ->
              let actuals1 =
                let uu____9284 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9284
>>>>>>> origin/master
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
<<<<<<< HEAD
                      (let uu____9351 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9351) in
=======
                      (let uu____9302 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9302) in
>>>>>>> origin/master
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
<<<<<<< HEAD
                      (let uu____9363 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____9363) in
                  let msg =
                    let uu____9368 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____9369 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9368 uu____9369 formals_msg actuals_msg in
=======
                      (let uu____9314 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____9314) in
                  let msg =
                    let uu____9319 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____9320 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9319 uu____9320 formals_msg actuals_msg in
>>>>>>> origin/master
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
<<<<<<< HEAD
          | uu____9374 ->
              let uu____9377 =
                let uu____9378 =
                  let uu____9381 =
                    let uu____9382 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____9383 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9382 uu____9383 in
                  (uu____9381, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____9378 in
              raise uu____9377 in
        let uu____9384 =
          FStar_List.fold_left
            (fun uu____9391  ->
               fun lb  ->
                 match uu____9391 with
                 | (lbs1,env1) ->
                     let uu____9403 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9403 with
=======
          | uu____9325 ->
              let uu____9328 =
                let uu____9329 =
                  let uu____9332 =
                    let uu____9333 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____9334 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9333 uu____9334 in
                  (uu____9332, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____9329 in
              raise uu____9328 in
        let uu____9335 =
          FStar_List.fold_left
            (fun uu____9342  ->
               fun lb  ->
                 match uu____9342 with
                 | (lbs1,env1) ->
                     let uu____9354 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9354 with
>>>>>>> origin/master
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
<<<<<<< HEAD
                              (let uu____9417 =
                                 let uu____9421 =
                                   let uu____9422 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left FStar_Pervasives.fst
                                     uu____9422 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___123_9427 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___123_9427.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___123_9427.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___123_9427.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___123_9427.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___123_9427.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___123_9427.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___123_9427.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___123_9427.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___123_9427.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___123_9427.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___123_9427.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___123_9427.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___123_9427.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___123_9427.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___123_9427.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___123_9427.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___123_9427.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___123_9427.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___123_9427.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___123_9427.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___123_9427.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___123_9427.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___123_9427.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____9421 in
                               match uu____9417 with
                               | (t1,uu____9429,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9433 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9433);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9435 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9435
                            then
                              let uu___124_9436 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___124_9436.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___124_9436.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___124_9436.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___124_9436.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___124_9436.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___124_9436.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___124_9436.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___124_9436.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___124_9436.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___124_9436.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___124_9436.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___124_9436.FStar_TypeChecker_Env.generalize);
=======
                              (let uu____9368 =
                                 let uu____9372 =
                                   let uu____9373 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left FStar_Pervasives.fst
                                     uu____9373 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___123_9378 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___123_9378.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___123_9378.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___123_9378.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___123_9378.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___123_9378.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___123_9378.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___123_9378.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___123_9378.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___123_9378.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___123_9378.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___123_9378.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___123_9378.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___123_9378.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___123_9378.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___123_9378.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___123_9378.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___123_9378.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___123_9378.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___123_9378.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___123_9378.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___123_9378.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___123_9378.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___123_9378.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____9372 in
                               match uu____9368 with
                               | (t1,uu____9380,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9384 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9384);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9386 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9386
                            then
                              let uu___124_9387 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___124_9387.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___124_9387.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___124_9387.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___124_9387.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___124_9387.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___124_9387.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___124_9387.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___124_9387.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___124_9387.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___124_9387.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___124_9387.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___124_9387.FStar_TypeChecker_Env.generalize);
>>>>>>> origin/master
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
<<<<<<< HEAD
                                  (uu___124_9436.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___124_9436.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___124_9436.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___124_9436.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___124_9436.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___124_9436.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___124_9436.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___124_9436.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___124_9436.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___124_9436.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___124_9436.FStar_TypeChecker_Env.qname_and_index)
=======
                                  (uu___124_9387.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___124_9387.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___124_9387.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___124_9387.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___124_9387.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___124_9387.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___124_9387.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___124_9387.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___124_9387.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___124_9387.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___124_9387.FStar_TypeChecker_Env.qname_and_index)
>>>>>>> origin/master
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
<<<<<<< HEAD
                            let uu___125_9446 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___125_9446.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___125_9446.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9384 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
=======
                            let uu___125_9397 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___125_9397.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___125_9397.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9335 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
>>>>>>> origin/master
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
<<<<<<< HEAD
      let uu____9460 =
        let uu____9465 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9477 =
                     let uu____9478 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____9478.FStar_Syntax_Syntax.n in
                   match uu____9477 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9481 -> ()
                   | uu____9496 ->
                       let uu____9497 =
                         let uu____9498 =
                           let uu____9501 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____9501) in
                         FStar_Errors.Error uu____9498 in
                       raise uu____9497);
                  (let uu____9502 =
                     let uu____9506 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____9506
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____9502 with
                   | (e,c,g) ->
                       ((let uu____9513 =
                           let uu____9514 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____9514 in
                         if uu____9513
=======
      let uu____9411 =
        let uu____9416 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9428 =
                     let uu____9429 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____9429.FStar_Syntax_Syntax.n in
                   match uu____9428 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9432 -> ()
                   | uu____9447 ->
                       let uu____9448 =
                         let uu____9449 =
                           let uu____9452 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____9452) in
                         FStar_Errors.Error uu____9449 in
                       raise uu____9448);
                  (let uu____9453 =
                     let uu____9457 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____9457
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____9453 with
                   | (e,c,g) ->
                       ((let uu____9464 =
                           let uu____9465 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____9465 in
                         if uu____9464
>>>>>>> origin/master
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
<<<<<<< HEAD
        FStar_All.pipe_right uu____9465 FStar_List.unzip in
      match uu____9460 with
=======
        FStar_All.pipe_right uu____9416 FStar_List.unzip in
      match uu____9411 with
>>>>>>> origin/master
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
<<<<<<< HEAD
        let uu____9543 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9543 with
        | (env1,uu____9553) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9559 = check_lbtyp top_level env lb in
            (match uu____9559 with
=======
        let uu____9494 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9494 with
        | (env1,uu____9504) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9510 = check_lbtyp top_level env lb in
            (match uu____9510 with
>>>>>>> origin/master
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
<<<<<<< HEAD
                   let uu____9585 =
                     tc_maybe_toplevel_term
                       (let uu___126_9589 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___126_9589.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___126_9589.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___126_9589.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___126_9589.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___126_9589.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___126_9589.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___126_9589.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___126_9589.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___126_9589.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___126_9589.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___126_9589.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___126_9589.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___126_9589.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___126_9589.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___126_9589.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___126_9589.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___126_9589.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___126_9589.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___126_9589.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___126_9589.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___126_9589.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___126_9589.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___126_9589.FStar_TypeChecker_Env.qname_and_index)
                        }) e11 in
                   match uu____9585 with
                   | (e12,c1,g1) ->
                       let uu____9598 =
                         let uu____9601 =
=======
                   let uu____9536 =
                     tc_maybe_toplevel_term
                       (let uu___126_9540 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___126_9540.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___126_9540.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___126_9540.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___126_9540.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___126_9540.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___126_9540.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___126_9540.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___126_9540.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___126_9540.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___126_9540.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___126_9540.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___126_9540.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___126_9540.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___126_9540.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___126_9540.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___126_9540.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___126_9540.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___126_9540.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___126_9540.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___126_9540.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___126_9540.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___126_9540.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___126_9540.FStar_TypeChecker_Env.qname_and_index)
                        }) e11 in
                   match uu____9536 with
                   | (e12,c1,g1) ->
                       let uu____9549 =
                         let uu____9552 =
>>>>>>> origin/master
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
<<<<<<< HEAD
                              (fun uu____9604  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9601 e12 c1 wf_annot in
                       (match uu____9598 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9614 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9614
                              then
                                let uu____9615 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9616 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9617 =
=======
                              (fun uu____9555  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9552 e12 c1 wf_annot in
                       (match uu____9549 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9565 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9565
                              then
                                let uu____9566 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9567 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9568 =
>>>>>>> origin/master
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
<<<<<<< HEAD
                                  uu____9615 uu____9616 uu____9617
=======
                                  uu____9566 uu____9567 uu____9568
>>>>>>> origin/master
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
<<<<<<< HEAD
        | uu____9643 ->
            let uu____9644 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9644 with
=======
        | uu____9594 ->
            let uu____9595 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9595 with
>>>>>>> origin/master
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
<<<<<<< HEAD
                   let uu____9671 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9671)
                 else
                   (let uu____9676 = FStar_Syntax_Util.type_u () in
                    match uu____9676 with
                    | (k,uu____9687) ->
                        let uu____9688 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9688 with
                         | (t2,uu____9700,g) ->
                             ((let uu____9703 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9703
                               then
                                 let uu____9704 =
                                   let uu____9705 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9705 in
                                 let uu____9706 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9704 uu____9706
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9709 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9709))))))
=======
                   let uu____9622 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9622)
                 else
                   (let uu____9627 = FStar_Syntax_Util.type_u () in
                    match uu____9627 with
                    | (k,uu____9638) ->
                        let uu____9639 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9639 with
                         | (t2,uu____9651,g) ->
                             ((let uu____9654 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9654
                               then
                                 let uu____9655 =
                                   let uu____9656 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9656 in
                                 let uu____9657 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9655 uu____9657
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9660 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9660))))))
>>>>>>> origin/master
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
<<<<<<< HEAD
    fun uu____9714  ->
      match uu____9714 with
      | (x,imp) ->
          let uu____9725 = FStar_Syntax_Util.type_u () in
          (match uu____9725 with
           | (tu,u) ->
               ((let uu____9737 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9737
                 then
                   let uu____9738 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9739 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9740 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9738 uu____9739 uu____9740
                 else ());
                (let uu____9742 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9742 with
                 | (t,uu____9753,g) ->
                     let x1 =
                       ((let uu___127_9758 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___127_9758.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___127_9758.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9760 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9760
                       then
                         let uu____9761 =
                           FStar_Syntax_Print.bv_to_string (fst x1) in
                         let uu____9762 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9761 uu____9762
                       else ());
                      (let uu____9764 = push_binding env x1 in
                       (x1, uu____9764, g, u))))))
=======
    fun uu____9665  ->
      match uu____9665 with
      | (x,imp) ->
          let uu____9676 = FStar_Syntax_Util.type_u () in
          (match uu____9676 with
           | (tu,u) ->
               ((let uu____9688 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9688
                 then
                   let uu____9689 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9690 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9691 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9689 uu____9690 uu____9691
                 else ());
                (let uu____9693 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9693 with
                 | (t,uu____9704,g) ->
                     let x1 =
                       ((let uu___127_9709 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___127_9709.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___127_9709.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9711 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9711
                       then
                         let uu____9712 =
                           FStar_Syntax_Print.bv_to_string (fst x1) in
                         let uu____9713 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9712 uu____9713
                       else ());
                      (let uu____9715 = push_binding env x1 in
                       (x1, uu____9715, g, u))))))
>>>>>>> origin/master
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
<<<<<<< HEAD
            let uu____9815 = tc_binder env1 b in
            (match uu____9815 with
             | (b1,env',g,u) ->
                 let uu____9838 = aux env' bs2 in
                 (match uu____9838 with
                  | (bs3,env'1,g',us) ->
                      let uu____9867 =
                        let uu____9868 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____9868 in
                      ((b1 :: bs3), env'1, uu____9867, (u :: us)))) in
=======
            let uu____9766 = tc_binder env1 b in
            (match uu____9766 with
             | (b1,env',g,u) ->
                 let uu____9789 = aux env' bs2 in
                 (match uu____9789 with
                  | (bs3,env'1,g',us) ->
                      let uu____9818 =
                        let uu____9819 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____9819 in
                      ((b1 :: bs3), env'1, uu____9818, (u :: us)))) in
>>>>>>> origin/master
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
<<<<<<< HEAD
          (fun uu____9911  ->
             fun uu____9912  ->
               match (uu____9911, uu____9912) with
               | ((t,imp),(args1,g)) ->
                   let uu____9949 = tc_term env1 t in
                   (match uu____9949 with
                    | (t1,uu____9959,g') ->
                        let uu____9961 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____9961))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9979  ->
             match uu____9979 with
             | (pats1,g) ->
                 let uu____9993 = tc_args env p in
                 (match uu____9993 with
                  | (args,g') ->
                      let uu____10001 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____10001))) pats
=======
          (fun uu____9862  ->
             fun uu____9863  ->
               match (uu____9862, uu____9863) with
               | ((t,imp),(args1,g)) ->
                   let uu____9900 = tc_term env1 t in
                   (match uu____9900 with
                    | (t1,uu____9910,g') ->
                        let uu____9912 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____9912))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9930  ->
             match uu____9930 with
             | (pats1,g) ->
                 let uu____9944 = tc_args env p in
                 (match uu____9944 with
                  | (args,g') ->
                      let uu____9952 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____9952))) pats
>>>>>>> origin/master
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
<<<<<<< HEAD
      let uu____10009 = tc_maybe_toplevel_term env e in
      match uu____10009 with
      | (e1,c,g) ->
          let uu____10019 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____10019
=======
      let uu____9960 = tc_maybe_toplevel_term env e in
      match uu____9960 with
      | (e1,c,g) ->
          let uu____9970 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____9970
>>>>>>> origin/master
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
<<<<<<< HEAD
             let uu____10029 =
               let uu____10032 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____10032
               then
                 let uu____10035 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____10035, false)
               else
                 (let uu____10037 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____10037, true)) in
             match uu____10029 with
             | (target_comp,allow_ghost) ->
                 let uu____10043 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____10043 with
                  | Some g' ->
                      let uu____10049 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____10049)
                  | uu____10050 ->
                      if allow_ghost
                      then
                        let uu____10055 =
                          let uu____10056 =
                            let uu____10059 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____10059, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____10056 in
                        raise uu____10055
                      else
                        (let uu____10064 =
                           let uu____10065 =
                             let uu____10068 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____10068, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____10065 in
                         raise uu____10064)))
=======
             let uu____9980 =
               let uu____9983 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____9983
               then
                 let uu____9986 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____9986, false)
               else
                 (let uu____9988 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____9988, true)) in
             match uu____9980 with
             | (target_comp,allow_ghost) ->
                 let uu____9994 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____9994 with
                  | Some g' ->
                      let uu____10000 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____10000)
                  | uu____10001 ->
                      if allow_ghost
                      then
                        let uu____10006 =
                          let uu____10007 =
                            let uu____10010 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____10010, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____10007 in
                        raise uu____10006
                      else
                        (let uu____10015 =
                           let uu____10016 =
                             let uu____10019 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____10019, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____10016 in
                         raise uu____10015)))
>>>>>>> origin/master
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
<<<<<<< HEAD
      let uu____10081 = tc_tot_or_gtot_term env t in
      match uu____10081 with
=======
      let uu____10032 = tc_tot_or_gtot_term env t in
      match uu____10032 with
>>>>>>> origin/master
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
<<<<<<< HEAD
      (let uu____10101 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10101
       then
         let uu____10102 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____10102
       else ());
      (let env1 =
         let uu___128_10105 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___128_10105.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___128_10105.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___128_10105.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___128_10105.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___128_10105.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___128_10105.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___128_10105.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___128_10105.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___128_10105.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___128_10105.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___128_10105.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___128_10105.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___128_10105.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___128_10105.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___128_10105.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___128_10105.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___128_10105.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___128_10105.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___128_10105.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___128_10105.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___128_10105.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____10108 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10124) ->
             let uu____10125 =
               let uu____10126 =
                 let uu____10129 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____10129) in
               FStar_Errors.Error uu____10126 in
             raise uu____10125 in
       match uu____10108 with
       | (t,c,g) ->
           let uu____10139 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____10139
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10146 =
                let uu____10147 =
                  let uu____10150 =
                    let uu____10151 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10151 in
                  let uu____10152 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____10150, uu____10152) in
                FStar_Errors.Error uu____10147 in
              raise uu____10146))
let level_of_type_fail env e t =
  let uu____10173 =
    let uu____10174 =
      let uu____10177 =
        let uu____10178 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10178 t in
      let uu____10179 = FStar_TypeChecker_Env.get_range env in
      (uu____10177, uu____10179) in
    FStar_Errors.Error uu____10174 in
  raise uu____10173
=======
      (let uu____10052 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10052
       then
         let uu____10053 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____10053
       else ());
      (let env1 =
         let uu___128_10056 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___128_10056.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___128_10056.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___128_10056.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___128_10056.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___128_10056.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___128_10056.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___128_10056.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___128_10056.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___128_10056.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___128_10056.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___128_10056.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___128_10056.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___128_10056.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___128_10056.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___128_10056.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___128_10056.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___128_10056.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___128_10056.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___128_10056.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___128_10056.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___128_10056.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____10059 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10075) ->
             let uu____10076 =
               let uu____10077 =
                 let uu____10080 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____10080) in
               FStar_Errors.Error uu____10077 in
             raise uu____10076 in
       match uu____10059 with
       | (t,c,g) ->
           let uu____10090 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____10090
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10097 =
                let uu____10098 =
                  let uu____10101 =
                    let uu____10102 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10102 in
                  let uu____10103 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____10101, uu____10103) in
                FStar_Errors.Error uu____10098 in
              raise uu____10097))
let level_of_type_fail env e t =
  let uu____10124 =
    let uu____10125 =
      let uu____10128 =
        let uu____10129 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10129 t in
      let uu____10130 = FStar_TypeChecker_Env.get_range env in
      (uu____10128, uu____10130) in
    FStar_Errors.Error uu____10125 in
  raise uu____10124
>>>>>>> origin/master
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
<<<<<<< HEAD
          let uu____10196 =
            let uu____10197 = FStar_Syntax_Util.unrefine t1 in
            uu____10197.FStar_Syntax_Syntax.n in
          match uu____10196 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10201 ->
=======
          let uu____10147 =
            let uu____10148 = FStar_Syntax_Util.unrefine t1 in
            uu____10148.FStar_Syntax_Syntax.n in
          match uu____10147 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10152 ->
>>>>>>> origin/master
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
<<<<<<< HEAD
                (let uu____10204 = FStar_Syntax_Util.type_u () in
                 match uu____10204 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___131_10210 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___131_10210.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___131_10210.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___131_10210.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___131_10210.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___131_10210.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___131_10210.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___131_10210.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___131_10210.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___131_10210.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___131_10210.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___131_10210.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___131_10210.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___131_10210.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___131_10210.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___131_10210.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___131_10210.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___131_10210.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___131_10210.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___131_10210.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___131_10210.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___131_10210.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___131_10210.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___131_10210.FStar_TypeChecker_Env.qname_and_index)
=======
                (let uu____10155 = FStar_Syntax_Util.type_u () in
                 match uu____10155 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___131_10161 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___131_10161.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___131_10161.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___131_10161.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___131_10161.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___131_10161.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___131_10161.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___131_10161.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___131_10161.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___131_10161.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___131_10161.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___131_10161.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___131_10161.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___131_10161.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___131_10161.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___131_10161.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___131_10161.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___131_10161.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___131_10161.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___131_10161.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___131_10161.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___131_10161.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___131_10161.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___131_10161.FStar_TypeChecker_Env.qname_and_index)
>>>>>>> origin/master
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
<<<<<<< HEAD
                           let uu____10214 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____10214
                       | uu____10215 ->
=======
                           let uu____10165 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____10165
                       | uu____10166 ->
>>>>>>> origin/master
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
<<<<<<< HEAD
      let uu____10224 =
        let uu____10225 = FStar_Syntax_Subst.compress e in
        uu____10225.FStar_Syntax_Syntax.n in
      match uu____10224 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10230 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10235 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10258 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10269) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10294,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10313) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10320 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10320 with | ((uu____10331,t),uu____10333) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10336,(FStar_Util.Inl t,uu____10338),uu____10339) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10375,(FStar_Util.Inr c,uu____10377),uu____10378) ->
=======
      let uu____10175 =
        let uu____10176 = FStar_Syntax_Subst.compress e in
        uu____10176.FStar_Syntax_Syntax.n in
      match uu____10175 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10181 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10186 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10209 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10220) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10245,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10260) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10267 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10267 with | ((uu____10278,t),uu____10280) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10283,(FStar_Util.Inl t,uu____10285),uu____10286) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10322,(FStar_Util.Inr c,uu____10324),uu____10325) ->
>>>>>>> origin/master
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)) None
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
<<<<<<< HEAD
             FStar_Syntax_Syntax.tk = uu____10421;
             FStar_Syntax_Syntax.pos = uu____10422;
             FStar_Syntax_Syntax.vars = uu____10423;_},us)
          ->
          let uu____10429 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10429 with
           | ((us',t),uu____10442) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10450 =
                     let uu____10451 =
                       let uu____10454 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10454) in
                     FStar_Errors.Error uu____10451 in
                   raise uu____10450)
=======
             FStar_Syntax_Syntax.tk = uu____10368;
             FStar_Syntax_Syntax.pos = uu____10369;
             FStar_Syntax_Syntax.vars = uu____10370;_},us)
          ->
          let uu____10376 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10376 with
           | ((us',t),uu____10389) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10397 =
                     let uu____10398 =
                       let uu____10401 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10401) in
                     FStar_Errors.Error uu____10398 in
                   raise uu____10397)
>>>>>>> origin/master
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
<<<<<<< HEAD
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10463 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10464 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10472) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10489 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10489 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10500  ->
                      match uu____10500 with
                      | (b,uu____10504) ->
                          let uu____10505 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10505) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10510 = universe_of_aux env res in
                 level_of_type env res uu____10510 in
               let u_c =
                 let uu____10512 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10512 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10515 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10515 in
=======
                             FStar_Unionfind.change u'' (Some u)
                         | uu____10409 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10410 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10418) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10435 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10435 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10446  ->
                      match uu____10446 with
                      | (b,uu____10450) ->
                          let uu____10451 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10451) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10456 = universe_of_aux env res in
                 level_of_type env res uu____10456 in
               let u_c =
                 let uu____10458 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10458 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10461 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10461 in
>>>>>>> origin/master
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
<<<<<<< HEAD
            | FStar_Syntax_Syntax.Tm_bvar uu____10585 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10595 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10625 ->
                let uu____10626 = universe_of_aux env hd3 in
                (uu____10626, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10636 ->
                let uu____10637 = universe_of_aux env hd3 in
                (uu____10637, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10647 ->
                let uu____10658 = universe_of_aux env hd3 in
                (uu____10658, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10668 ->
                let uu____10673 = universe_of_aux env hd3 in
                (uu____10673, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10683 ->
                let uu____10701 = universe_of_aux env hd3 in
                (uu____10701, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10711 ->
                let uu____10716 = universe_of_aux env hd3 in
                (uu____10716, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10726 ->
                let uu____10727 = universe_of_aux env hd3 in
                (uu____10727, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10737 ->
                let uu____10745 = universe_of_aux env hd3 in
                (uu____10745, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____10755 ->
                let uu____10760 = universe_of_aux env hd3 in
                (uu____10760, args1)
            | FStar_Syntax_Syntax.Tm_type uu____10770 ->
                let uu____10771 = universe_of_aux env hd3 in
                (uu____10771, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10781,hd4::uu____10783) ->
                let uu____10830 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____10830 with
                 | (uu____10840,uu____10841,hd5) ->
                     let uu____10857 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____10857 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10892 when retry ->
=======
            | FStar_Syntax_Syntax.Tm_bvar uu____10531 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10541 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10571 ->
                let uu____10572 = universe_of_aux env hd3 in
                (uu____10572, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10582 ->
                let uu____10583 = universe_of_aux env hd3 in
                (uu____10583, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10593 ->
                let uu____10602 = universe_of_aux env hd3 in
                (uu____10602, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10612 ->
                let uu____10617 = universe_of_aux env hd3 in
                (uu____10617, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10627 ->
                let uu____10645 = universe_of_aux env hd3 in
                (uu____10645, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10655 ->
                let uu____10660 = universe_of_aux env hd3 in
                (uu____10660, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10670 ->
                let uu____10671 = universe_of_aux env hd3 in
                (uu____10671, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10681 ->
                let uu____10689 = universe_of_aux env hd3 in
                (uu____10689, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____10699 ->
                let uu____10704 = universe_of_aux env hd3 in
                (uu____10704, args1)
            | FStar_Syntax_Syntax.Tm_type uu____10714 ->
                let uu____10715 = universe_of_aux env hd3 in
                (uu____10715, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10725,hd4::uu____10727) ->
                let uu____10774 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____10774 with
                 | (uu____10784,uu____10785,hd5) ->
                     let uu____10801 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____10801 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10836 when retry ->
>>>>>>> origin/master
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
<<<<<<< HEAD
                let uu____10894 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____10894 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10929 ->
                let uu____10930 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____10930 with
                 | (env1,uu____10944) ->
                     let env2 =
                       let uu___132_10948 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___132_10948.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___132_10948.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___132_10948.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___132_10948.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___132_10948.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___132_10948.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___132_10948.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___132_10948.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___132_10948.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___132_10948.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___132_10948.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___132_10948.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___132_10948.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___132_10948.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___132_10948.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___132_10948.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___132_10948.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___132_10948.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___132_10948.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___132_10948.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___132_10948.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     ((let uu____10950 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____10950
                       then
                         let uu____10951 =
                           let uu____10952 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____10952 in
                         let uu____10953 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10951 uu____10953
                       else ());
                      (let uu____10955 = tc_term env2 hd3 in
                       match uu____10955 with
                       | (uu____10968,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10969;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10971;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10972;_},g)
                           ->
                           ((let uu____10982 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____10982
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____10990 = type_of_head true hd1 args in
          (match uu____10990 with
=======
                let uu____10838 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____10838 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10873 ->
                let uu____10874 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____10874 with
                 | (env1,uu____10888) ->
                     let env2 =
                       let uu___132_10892 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___132_10892.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___132_10892.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___132_10892.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___132_10892.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___132_10892.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___132_10892.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___132_10892.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___132_10892.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___132_10892.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___132_10892.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___132_10892.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___132_10892.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___132_10892.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___132_10892.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___132_10892.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___132_10892.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___132_10892.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___132_10892.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___132_10892.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___132_10892.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___132_10892.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     ((let uu____10894 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____10894
                       then
                         let uu____10895 =
                           let uu____10896 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____10896 in
                         let uu____10897 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10895 uu____10897
                       else ());
                      (let uu____10899 = tc_term env2 hd3 in
                       match uu____10899 with
                       | (uu____10912,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10913;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10915;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10916;_},g)
                           ->
                           ((let uu____10926 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____10926
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____10934 = type_of_head true hd1 args in
          (match uu____10934 with
>>>>>>> origin/master
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
<<<<<<< HEAD
               let uu____11019 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____11019 with
=======
               let uu____10963 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____10963 with
>>>>>>> origin/master
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
<<<<<<< HEAD
                      (let uu____11052 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____11052)))
      | FStar_Syntax_Syntax.Tm_match (uu____11055,hd1::uu____11057) ->
          let uu____11104 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____11104 with
           | (uu____11107,uu____11108,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11124,[]) ->
=======
                      (let uu____10996 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____10996)))
      | FStar_Syntax_Syntax.Tm_match (uu____10999,hd1::uu____11001) ->
          let uu____11048 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____11048 with
           | (uu____11051,uu____11052,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11068,[]) ->
>>>>>>> origin/master
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
<<<<<<< HEAD
      let uu____11158 = universe_of_aux env e in
      level_of_type env e uu____11158
=======
      let uu____11102 = universe_of_aux env e in
      level_of_type env e uu____11102
>>>>>>> origin/master
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
<<<<<<< HEAD
      let uu____11171 = tc_binders env tps in
      match uu____11171 with
=======
      let uu____11115 = tc_binders env tps in
      match uu____11115 with
>>>>>>> origin/master
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))