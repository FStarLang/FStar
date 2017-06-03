open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___88_4 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___88_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___88_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___88_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___88_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___88_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___88_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___88_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___88_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___88_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___88_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___88_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___88_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___88_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___88_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___88_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___88_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___88_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___88_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___88_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___88_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___88_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___88_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___88_4.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___88_4.FStar_TypeChecker_Env.proof_ns)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___89_8 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___89_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___89_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___89_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___89_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___89_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___89_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___89_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___89_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___89_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___89_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___89_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___89_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___89_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___89_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___89_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___89_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___89_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___89_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___89_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___89_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___89_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___89_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___89_8.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___89_8.FStar_TypeChecker_Env.proof_ns)
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
  fun uu___83_47  ->
    match uu___83_47 with
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
      let uu___90_175 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___90_175.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___90_175.FStar_Syntax_Syntax.cflags);
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
                 let uu___91_661 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___91_661.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___91_661.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___91_661.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___91_661.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___91_661.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___91_661.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___91_661.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___91_661.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___91_661.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___91_661.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___91_661.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___91_661.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___91_661.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___91_661.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___91_661.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___91_661.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___91_661.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___91_661.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___91_661.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___91_661.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___91_661.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___91_661.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___91_661.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___91_661.FStar_TypeChecker_Env.proof_ns)
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
                        (fun uu___84_742  ->
                           match uu___84_742 with
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
                                      let uu___92_875 = last1 in
                                      let uu____876 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___92_875.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___92_875.FStar_Syntax_Syntax.index);
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
        (let uu___93_1172 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___93_1172.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___93_1172.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___93_1172.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___93_1172.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___93_1172.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___93_1172.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___93_1172.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___93_1172.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___93_1172.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___93_1172.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___93_1172.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___93_1172.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___93_1172.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___93_1172.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___93_1172.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___93_1172.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___93_1172.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___93_1172.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___93_1172.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___93_1172.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___93_1172.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___93_1172.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___93_1172.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___93_1172.FStar_TypeChecker_Env.proof_ns)
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
                  let uu___94_1277 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___94_1277.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___94_1277.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___94_1277.FStar_TypeChecker_Env.implicits)
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
                            let uu___95_1351 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___95_1351.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___95_1351.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___95_1351.FStar_TypeChecker_Env.implicits)
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
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.quote_lid
                   -> true
               | uu____2573 -> false in
             let uu____2574 = tc_term (no_inst env2) head1 in
             match uu____2574 with
             | (head2,chead,g_head) ->
                 let uu____2584 =
                   let uu____2588 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2588
                   then
                     let uu____2592 =
                       let uu____2596 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____2596 in
                     match uu____2592 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____2605 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____2606 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____2606))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____2605
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____2611 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____2611) in
                 (match uu____2584 with
                  | (e1,c,g) ->
                      ((let uu____2620 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2620
                        then
                          let uu____2621 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2621
                        else ());
                       (let uu____2623 = comp_check_expected_typ env0 e1 c in
                        match uu____2623 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____2634 =
                                let uu____2635 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2635.FStar_Syntax_Syntax.n in
                              match uu____2634 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2639) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___96_2671 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___96_2671.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___96_2671.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___96_2671.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2696 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2698 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2698 in
                            ((let uu____2700 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2700
                              then
                                let uu____2701 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2702 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2701 uu____2702
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2732 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2732 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2744 = tc_term env12 e1 in
                (match uu____2744 with
                 | (e11,c1,g1) ->
                     let uu____2754 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2760 = FStar_Syntax_Util.type_u () in
                           (match uu____2760 with
                            | (k,uu____2766) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2768 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2768, res_t)) in
                     (match uu____2754 with
                      | (env_branches,res_t) ->
                          ((let uu____2775 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2775
                            then
                              let uu____2776 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2776
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2827 =
                              let uu____2830 =
                                FStar_List.fold_right
                                  (fun uu____2849  ->
                                     fun uu____2850  ->
                                       match (uu____2849, uu____2850) with
                                       | ((uu____2882,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2915 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____2915))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2830 with
                              | (cases,g) ->
                                  let uu____2936 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____2936, g) in
                            match uu____2827 with
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
                                           (fun uu____2989  ->
                                              match uu____2989 with
                                              | ((pat,wopt,br),uu____3005,lc,uu____3007)
                                                  ->
                                                  let uu____3014 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____3014))) in
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
                                  let uu____3070 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____3070
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____3077 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____3077 in
                                     let lb =
                                       let uu____3081 =
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
                                           uu____3081;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____3085 =
                                         let uu____3088 =
                                           let uu____3089 =
                                             let uu____3097 =
                                               let uu____3098 =
                                                 let uu____3099 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____3099] in
                                               FStar_Syntax_Subst.close
                                                 uu____3098 e_match in
                                             ((false, [lb]), uu____3097) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____3089 in
                                         FStar_Syntax_Syntax.mk uu____3088 in
                                       uu____3085
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____3113 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____3113
                                  then
                                    let uu____3114 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____3115 =
                                      let uu____3116 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____3116 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____3114 uu____3115
                                  else ());
                                 (let uu____3118 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____3118))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3121;
                FStar_Syntax_Syntax.lbunivs = uu____3122;
                FStar_Syntax_Syntax.lbtyp = uu____3123;
                FStar_Syntax_Syntax.lbeff = uu____3124;
                FStar_Syntax_Syntax.lbdef = uu____3125;_}::[]),uu____3126)
           ->
           ((let uu____3141 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3141
             then
               let uu____3142 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3142
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____3144),uu____3145) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3155;
                FStar_Syntax_Syntax.lbunivs = uu____3156;
                FStar_Syntax_Syntax.lbtyp = uu____3157;
                FStar_Syntax_Syntax.lbeff = uu____3158;
                FStar_Syntax_Syntax.lbdef = uu____3159;_}::uu____3160),uu____3161)
           ->
           ((let uu____3177 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3177
             then
               let uu____3178 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3178
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3180),uu____3181) ->
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
          let uu____3204 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3204 with
           | (tactic1,uu____3210,uu____3211) -> Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____3246 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3246 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3259 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3259
              then FStar_Util.Inl t1
              else
                (let uu____3263 =
                   let uu____3264 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3264 in
                 FStar_Util.Inr uu____3263) in
            let is_data_ctor uu___85_3273 =
              match uu___85_3273 with
              | Some (FStar_Syntax_Syntax.Data_ctor ) -> true
              | Some (FStar_Syntax_Syntax.Record_ctor uu____3275) -> true
              | uu____3279 -> false in
            let uu____3281 =
              (is_data_ctor dc) &&
                (let uu____3282 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3282) in
            if uu____3281
            then
              let uu____3288 =
                let uu____3289 =
                  let uu____3292 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3295 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3292, uu____3295) in
                FStar_Errors.Error uu____3289 in
              raise uu____3288
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3306 =
            let uu____3307 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3307 in
          failwith uu____3306
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3326 =
              let uu____3327 = FStar_Syntax_Subst.compress t1 in
              uu____3327.FStar_Syntax_Syntax.n in
            match uu____3326 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3330 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3338 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___97_3358 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___97_3358.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___97_3358.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___97_3358.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3386 =
            let uu____3393 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3393 with
            | None  ->
                let uu____3401 = FStar_Syntax_Util.type_u () in
                (match uu____3401 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3386 with
           | (t,uu____3422,g0) ->
               let uu____3430 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3430 with
                | (e1,uu____3441,g1) ->
                    let uu____3449 =
                      let uu____3450 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3450
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3451 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3449, uu____3451)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3453 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3462 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3462)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3453 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___98_3476 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___98_3476.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___98_3476.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3479 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3479 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3492 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3492
                       then FStar_Util.Inl t1
                       else
                         (let uu____3496 =
                            let uu____3497 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3497 in
                          FStar_Util.Inr uu____3496) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3503;
             FStar_Syntax_Syntax.pos = uu____3504;
             FStar_Syntax_Syntax.vars = uu____3505;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3513 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3513 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3539 =
                     let uu____3540 =
                       let uu____3543 = FStar_TypeChecker_Env.get_range env1 in
                       ("Unexpected number of universe instantiations",
                         uu____3543) in
                     FStar_Errors.Error uu____3540 in
                   raise uu____3539)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____3550 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___99_3552 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___100_3553 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___100_3553.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___100_3553.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___99_3552.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___99_3552.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3569 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3569 us1 in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3581 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3581 with
           | ((us,t),range) ->
               ((let uu____3599 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3599
                 then
                   let uu____3600 =
                     let uu____3601 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3601 in
                   let uu____3602 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3603 = FStar_Range.string_of_range range in
                   let uu____3604 = FStar_Range.string_of_use_range range in
                   let uu____3605 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
                     uu____3600 uu____3602 uu____3603 uu____3604 uu____3605
                 else ());
                (let fv' =
                   let uu___101_3608 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___102_3609 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___102_3609.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___102_3609.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___101_3608.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___101_3608.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3625 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3625 us in
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
          let uu____3661 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3661 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3670 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3670 with
                | (env2,uu____3678) ->
                    let uu____3681 = tc_binders env2 bs1 in
                    (match uu____3681 with
                     | (bs2,env3,g,us) ->
                         let uu____3693 = tc_comp env3 c1 in
                         (match uu____3693 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___103_3706 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___103_3706.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___103_3706.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___103_3706.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____3727 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3727 in
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
          let uu____3762 =
            let uu____3765 =
              let uu____3766 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3766] in
            FStar_Syntax_Subst.open_term uu____3765 phi in
          (match uu____3762 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____3773 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3773 with
                | (env2,uu____3781) ->
                    let uu____3784 =
                      let uu____3791 = FStar_List.hd x1 in
                      tc_binder env2 uu____3791 in
                    (match uu____3784 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3808 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____3808
                           then
                             let uu____3809 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____3810 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____3811 =
                               FStar_Syntax_Print.bv_to_string (fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3809 uu____3810 uu____3811
                           else ());
                          (let uu____3813 = FStar_Syntax_Util.type_u () in
                           match uu____3813 with
                           | (t_phi,uu____3820) ->
                               let uu____3821 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____3821 with
                                | (phi2,uu____3829,f2) ->
                                    let e1 =
                                      let uu___104_3834 =
                                        FStar_Syntax_Util.refine (fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___104_3834.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___104_3834.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___104_3834.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____3853 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3853 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3862) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____3887 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____3887
            then
              let uu____3888 =
                FStar_Syntax_Print.term_to_string
                  (let uu___105_3889 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___105_3889.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___105_3889.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___105_3889.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3888
            else ());
           (let uu____3908 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____3908 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3916 ->
          let uu____3917 =
            let uu____3918 = FStar_Syntax_Print.term_to_string top in
            let uu____3919 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3918
              uu____3919 in
          failwith uu____3917
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3925 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3926,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3932,Some uu____3933) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3941 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3945 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3946 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3947 ->
          FStar_TypeChecker_Common.t_range
      | uu____3948 -> raise (FStar_Errors.Error ("Unsupported constant", r))
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
      | FStar_Syntax_Syntax.Total (t,uu____3959) ->
          let uu____3966 = FStar_Syntax_Util.type_u () in
          (match uu____3966 with
           | (k,u) ->
               let uu____3974 = tc_check_tot_or_gtot_term env t k in
               (match uu____3974 with
                | (t1,uu____3982,g) ->
                    let uu____3984 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____3984, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3986) ->
          let uu____3993 = FStar_Syntax_Util.type_u () in
          (match uu____3993 with
           | (k,u) ->
               let uu____4001 = tc_check_tot_or_gtot_term env t k in
               (match uu____4001 with
                | (t1,uu____4009,g) ->
                    let uu____4011 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____4011, u, g)))
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
            let uu____4027 =
              let uu____4028 =
                let uu____4029 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____4029 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____4028 in
            uu____4027 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____4034 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____4034 with
           | (tc1,uu____4042,f) ->
               let uu____4044 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____4044 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4074 =
                        let uu____4075 = FStar_Syntax_Subst.compress head3 in
                        uu____4075.FStar_Syntax_Syntax.n in
                      match uu____4074 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4078,us) -> us
                      | uu____4084 -> [] in
                    let uu____4085 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____4085 with
                     | (uu____4098,args1) ->
                         let uu____4114 =
                           let uu____4126 = FStar_List.hd args1 in
                           let uu____4135 = FStar_List.tl args1 in
                           (uu____4126, uu____4135) in
                         (match uu____4114 with
                          | (res,args2) ->
                              let uu____4177 =
                                let uu____4182 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___86_4192  ->
                                          match uu___86_4192 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4198 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4198 with
                                               | (env1,uu____4205) ->
                                                   let uu____4208 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4208 with
                                                    | (e1,uu____4215,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____4182
                                  FStar_List.unzip in
                              (match uu____4177 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___106_4238 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___106_4238.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___106_4238.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4242 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4242 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____4245 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4245))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4253 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4254 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4258 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4258
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4261 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4261
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4265 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4265 FStar_Pervasives.snd
         | uu____4270 -> aux u)
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
            let uu____4291 =
              let uu____4292 =
                let uu____4295 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4295, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4292 in
            raise uu____4291 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4349 bs2 bs_expected1 =
              match uu____4349 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit
                            uu____4440)) ->
                             let uu____4443 =
                               let uu____4444 =
                                 let uu____4447 =
                                   let uu____4448 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4448 in
                                 let uu____4449 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4447, uu____4449) in
                               FStar_Errors.Error uu____4444 in
                             raise uu____4443
                         | (Some (FStar_Syntax_Syntax.Implicit
                            uu____4450),None ) ->
                             let uu____4453 =
                               let uu____4454 =
                                 let uu____4457 =
                                   let uu____4458 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4458 in
                                 let uu____4459 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4457, uu____4459) in
                               FStar_Errors.Error uu____4454 in
                             raise uu____4453
                         | uu____4460 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4464 =
                           let uu____4467 =
                             let uu____4468 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4468.FStar_Syntax_Syntax.n in
                           match uu____4467 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4473 ->
                               ((let uu____4475 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4475
                                 then
                                   let uu____4476 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4476
                                 else ());
                                (let uu____4478 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4478 with
                                 | (t,uu____4485,g1) ->
                                     let g2 =
                                       let uu____4488 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4489 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4488
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4489 in
                                     let g3 =
                                       let uu____4491 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4491 in
                                     (t, g3))) in
                         match uu____4464 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___107_4507 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___107_4507.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___107_4507.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4516 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4516 in
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
                  | uu____4618 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4622 = tc_binders env1 bs in
                  match uu____4622 with
                  | (bs1,envbody,g,uu____4643) ->
                      let uu____4644 =
                        let uu____4651 =
                          let uu____4652 = FStar_Syntax_Subst.compress body1 in
                          uu____4652.FStar_Syntax_Syntax.n in
                        match uu____4651 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4664) ->
                            let uu____4700 = tc_comp envbody c in
                            (match uu____4700 with
                             | (c1,uu____4711,g') ->
                                 let uu____4713 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4715 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), uu____4713, body1, uu____4715))
                        | uu____4718 -> (None, None, body1, g) in
                      (match uu____4644 with
                       | (copt,tacopt,body2,g1) ->
                           (None, bs1, [], copt, tacopt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____4777 =
                    let uu____4778 = FStar_Syntax_Subst.compress t2 in
                    uu____4778.FStar_Syntax_Syntax.n in
                  match uu____4777 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____4795 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4807 -> failwith "Impossible");
                       (let uu____4811 = tc_binders env1 bs in
                        match uu____4811 with
                        | (bs1,envbody,g,uu____4833) ->
                            let uu____4834 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4834 with
                             | (envbody1,uu____4853) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____4864;
                         FStar_Syntax_Syntax.tk = uu____4865;
                         FStar_Syntax_Syntax.pos = uu____4866;
                         FStar_Syntax_Syntax.vars = uu____4867;_},uu____4868)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4894 -> failwith "Impossible");
                       (let uu____4898 = tc_binders env1 bs in
                        match uu____4898 with
                        | (bs1,envbody,g,uu____4920) ->
                            let uu____4921 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4921 with
                             | (envbody1,uu____4940) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4952) ->
                      let uu____4957 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____4957 with
                       | (uu____4986,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____5026 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____5026 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5089 c_expected2 =
                               match uu____5089 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____5150 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____5150)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____5167 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5167 in
                                        let uu____5168 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____5168)
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
                                               let uu____5209 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____5209 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5221 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____5221 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5248 =
                                                           let uu____5264 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____5264,
                                                             subst2) in
                                                         handle_more
                                                           uu____5248
                                                           c_expected4))
                                           | uu____5273 ->
                                               let uu____5274 =
                                                 let uu____5275 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____5275 in
                                               fail uu____5274 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____5291 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5291 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___108_5329 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___108_5329.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___108_5329.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___108_5329.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___108_5329.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___108_5329.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___108_5329.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___108_5329.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___108_5329.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___108_5329.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___108_5329.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___108_5329.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___108_5329.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___108_5329.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___108_5329.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___108_5329.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___108_5329.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___108_5329.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___108_5329.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___108_5329.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___108_5329.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___108_5329.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___108_5329.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___108_5329.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___108_5329.FStar_TypeChecker_Env.proof_ns)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5343  ->
                                     fun uu____5344  ->
                                       match (uu____5343, uu____5344) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5369 =
                                             let uu____5373 =
                                               let uu____5374 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5374
                                                 FStar_Pervasives.fst in
                                             tc_term uu____5373 t3 in
                                           (match uu____5369 with
                                            | (t4,uu____5386,uu____5387) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5394 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___109_5395
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___109_5395.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___109_5395.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5394 ::
                                                        letrec_binders
                                                  | uu____5396 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5399 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5399 with
                            | (envbody,bs1,g,c) ->
                                let uu____5431 =
                                  let uu____5435 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5435
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5431 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), None, envbody2, body1, g))))
                  | uu____5471 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5486 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5486
                      else
                        (let uu____5488 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5488 with
                         | (uu____5516,bs1,uu____5518,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, tacopt,
                               envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5543 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5543 with
          | (env1,topt) ->
              ((let uu____5555 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5555
                then
                  let uu____5556 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5556
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5560 = expected_function_typ1 env1 topt body in
                match uu____5560 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5595 =
                      tc_term
                        (let uu___110_5599 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___110_5599.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___110_5599.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___110_5599.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___110_5599.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___110_5599.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___110_5599.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___110_5599.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___110_5599.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___110_5599.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___110_5599.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___110_5599.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___110_5599.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___110_5599.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___110_5599.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___110_5599.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___110_5599.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___110_5599.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___110_5599.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___110_5599.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___110_5599.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___110_5599.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___110_5599.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___110_5599.FStar_TypeChecker_Env.proof_ns)
                         }) body1 in
                    (match uu____5595 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5608 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5608
                           then
                             let uu____5609 =
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
                               uu____5609 uu____5620
                           else ());
                          (let uu____5623 =
                             let uu____5627 =
                               let uu____5630 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5630) in
                             check_expected_effect
                               (let uu___111_5635 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___111_5635.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___111_5635.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___111_5635.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___111_5635.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___111_5635.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___111_5635.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___111_5635.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___111_5635.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___111_5635.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___111_5635.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___111_5635.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___111_5635.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___111_5635.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___111_5635.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___111_5635.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___111_5635.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___111_5635.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___111_5635.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___111_5635.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___111_5635.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___111_5635.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___111_5635.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___111_5635.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___111_5635.FStar_TypeChecker_Env.proof_ns)
                                }) c_opt uu____5627 in
                           match uu____5623 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
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
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5649 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
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
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
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
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____5732 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____5732 with
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
              (let uu____5769 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____5769
               then
                 let uu____5770 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____5771 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5770
                   uu____5771
               else ());
              (let monadic_application uu____5809 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____5809 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___112_5846 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___112_5846.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___112_5846.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___112_5846.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____5847 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____5856 ->
                           let g =
                             let uu____5861 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____5861
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____5862 =
                             let uu____5863 =
                               let uu____5866 =
                                 let uu____5867 =
                                   let uu____5868 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____5868 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5867 in
                               FStar_Syntax_Syntax.mk_Total uu____5866 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5863 in
                           (uu____5862, g) in
                     (match uu____5847 with
                      | (cres2,guard1) ->
                          ((let uu____5879 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____5879
                            then
                              let uu____5880 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5880
                            else ());
                           (let cres3 =
                              let uu____5883 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____5883
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
                                   fun uu____5906  ->
                                     match uu____5906 with
                                     | ((e,q),x,c) ->
                                         let uu____5929 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____5929
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
                              let uu____5938 =
                                let uu____5939 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____5939.FStar_Syntax_Syntax.n in
                              match uu____5938 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____5943 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____5953  ->
                                         match uu____5953 with
                                         | (arg,uu____5961,uu____5962) -> arg
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
                                (let uu____5974 =
                                   let map_fun uu____6009 =
                                     match uu____6009 with
                                     | ((e,q),uu____6029,c) ->
                                         let uu____6035 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6035
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
                                            let uu____6065 =
                                              let uu____6068 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____6068, q) in
                                            ((Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____6065)) in
                                   let uu____6086 =
                                     let uu____6100 =
                                       let uu____6113 =
                                         let uu____6121 =
                                           let uu____6126 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____6126, None, chead1) in
                                         uu____6121 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____6113 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6100 in
                                   match uu____6086 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6221 =
                                         let uu____6222 =
                                           FStar_List.hd reverse_args in
                                         fst uu____6222 in
                                       let uu____6227 =
                                         let uu____6231 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6231 in
                                       (lifted_args, uu____6221, uu____6227) in
                                 match uu____5974 with
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
                                     let bind_lifted_args e uu___87_6299 =
                                       match uu___87_6299 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6341 =
                                               let uu____6344 =
                                                 let uu____6345 =
                                                   let uu____6353 =
                                                     let uu____6354 =
                                                       let uu____6355 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6355] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6354 e in
                                                   ((false, [lb]),
                                                     uu____6353) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6345 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6344 in
                                             uu____6341 None
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
                            let uu____6389 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6389 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6443 bs args1 =
                 match uu____6443 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6526))::rest,
                         (uu____6528,None )::uu____6529) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 = check_no_escape (Some head1) env fvs t in
                          let uu____6566 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6566 with
                           | (varg,uu____6577,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6590 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6590) in
                               let uu____6591 =
                                 let uu____6609 =
                                   let uu____6617 =
                                     let uu____6624 =
                                       let uu____6625 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____6625
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, None, uu____6624) in
                                   uu____6617 :: outargs in
                                 let uu____6635 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____6609, (arg :: arg_rets),
                                   uu____6635, fvs) in
                               tc_args head_info uu____6591 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit
                               uu____6695),Some (FStar_Syntax_Syntax.Implicit
                               uu____6696)) -> ()
                            | (None ,None ) -> ()
                            | (Some (FStar_Syntax_Syntax.Equality ),None ) ->
                                ()
                            | uu____6703 ->
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___113_6710 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___113_6710.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___113_6710.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6712 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6712
                             then
                               let uu____6713 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6713
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___114_6718 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___114_6718.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___114_6718.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___114_6718.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___114_6718.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___114_6718.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___114_6718.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___114_6718.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___114_6718.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___114_6718.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___114_6718.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___114_6718.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___114_6718.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___114_6718.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___114_6718.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___114_6718.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___114_6718.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___114_6718.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___114_6718.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___114_6718.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___114_6718.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___114_6718.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___114_6718.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___114_6718.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___114_6718.FStar_TypeChecker_Env.proof_ns)
                               } in
                             (let uu____6720 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6720
                              then
                                let uu____6721 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6722 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6723 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6721 uu____6722 uu____6723
                              else ());
                             (let uu____6725 = tc_term env2 e in
                              match uu____6725 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____6742 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____6742 in
                                  let uu____6743 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____6743
                                  then
                                    let subst2 =
                                      let uu____6748 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6748 e1 in
                                    tc_args head_info
                                      (subst2, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        (x1 :: fvs)) rest rest'))))
                      | (uu____6796,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6817) ->
                          let uu____6847 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____6847 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6870 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____6870
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____6886 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____6886 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____6900 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____6900
                                            then
                                              let uu____6901 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____6901
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____6923 when Prims.op_Negation norm1 ->
                                     let uu____6924 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____6924
                                 | uu____6925 ->
                                     let uu____6926 =
                                       let uu____6927 =
                                         let uu____6930 =
                                           let uu____6931 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____6932 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6931 uu____6932 in
                                         let uu____6939 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____6930, uu____6939) in
                                       FStar_Errors.Error uu____6927 in
                                     raise uu____6926 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____6952 =
                   let uu____6953 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____6953.FStar_Syntax_Syntax.n in
                 match uu____6952 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____6961 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7025 = tc_term env1 e in
                           (match uu____7025 with
                            | (e1,c,g_e) ->
                                let uu____7038 = tc_args1 env1 tl1 in
                                (match uu____7038 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7060 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7060))) in
                     let uu____7071 = tc_args1 env args in
                     (match uu____7071 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7093 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7113  ->
                                      match uu____7113 with
                                      | (uu____7121,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7093 in
                          let ml_or_tot t r1 =
                            let uu____7137 = FStar_Options.ml_ish () in
                            if uu____7137
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7140 =
                              let uu____7143 =
                                let uu____7144 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7144
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7143 in
                            ml_or_tot uu____7140 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7153 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7153
                            then
                              let uu____7154 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7155 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7156 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7154 uu____7155 uu____7156
                            else ());
                           (let uu____7159 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7159);
                           (let comp =
                              let uu____7161 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7166  ->
                                   fun out  ->
                                     match uu____7166 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7161 in
                            let uu____7175 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7182 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7175, comp, uu____7182))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7185;
                        FStar_Syntax_Syntax.tk = uu____7186;
                        FStar_Syntax_Syntax.pos = uu____7187;
                        FStar_Syntax_Syntax.vars = uu____7188;_},uu____7189)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7267 = tc_term env1 e in
                           (match uu____7267 with
                            | (e1,c,g_e) ->
                                let uu____7280 = tc_args1 env1 tl1 in
                                (match uu____7280 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7302 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7302))) in
                     let uu____7313 = tc_args1 env args in
                     (match uu____7313 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7335 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7355  ->
                                      match uu____7355 with
                                      | (uu____7363,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7335 in
                          let ml_or_tot t r1 =
                            let uu____7379 = FStar_Options.ml_ish () in
                            if uu____7379
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7382 =
                              let uu____7385 =
                                let uu____7386 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7386
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7385 in
                            ml_or_tot uu____7382 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7395 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7395
                            then
                              let uu____7396 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7397 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7398 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7396 uu____7397 uu____7398
                            else ());
                           (let uu____7401 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7401);
                           (let comp =
                              let uu____7403 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7408  ->
                                   fun out  ->
                                     match uu____7408 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7403 in
                            let uu____7417 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7424 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7417, comp, uu____7424))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7439 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7439 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7475) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7481,uu____7482)
                     -> check_function_app t
                 | uu____7511 ->
                     let uu____7512 =
                       let uu____7513 =
                         let uu____7516 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7516, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7513 in
                     raise uu____7512 in
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
                  let uu____7571 =
                    FStar_List.fold_left2
                      (fun uu____7584  ->
                         fun uu____7585  ->
                           fun uu____7586  ->
                             match (uu____7584, uu____7585, uu____7586) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7630 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7630 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7642 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7642 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7644 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7644) &&
                                              (let uu____7645 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7645)) in
                                       let uu____7646 =
                                         let uu____7652 =
                                           let uu____7658 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7658] in
                                         FStar_List.append seen uu____7652 in
                                       let uu____7663 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7646, uu____7663, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7571 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____7692 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7692
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7694 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7694 with | (c2,g) -> (e, c2, g)))
              | uu____7706 ->
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
        let uu____7728 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7728 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7754 = branch1 in
            (match uu____7754 with
             | (cpat,uu____7774,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7812 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____7812 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____7829 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____7829
                         then
                           let uu____7830 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____7831 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7830 uu____7831
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____7834 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____7834 with
                         | (env1,uu____7845) ->
                             let env11 =
                               let uu___115_7849 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___115_7849.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___115_7849.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___115_7849.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___115_7849.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___115_7849.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___115_7849.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___115_7849.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___115_7849.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___115_7849.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___115_7849.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___115_7849.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___115_7849.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___115_7849.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___115_7849.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___115_7849.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___115_7849.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___115_7849.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___115_7849.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___115_7849.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___115_7849.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___115_7849.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___115_7849.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___115_7849.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___115_7849.FStar_TypeChecker_Env.proof_ns)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____7852 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____7852
                               then
                                 let uu____7853 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____7854 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____7853 uu____7854
                               else ());
                              (let uu____7856 = tc_tot_or_gtot_term env11 exp in
                               match uu____7856 with
                               | (exp1,lc,g) ->
                                   let g' =
                                     FStar_TypeChecker_Rel.teq env11
                                       lc.FStar_Syntax_Syntax.res_typ
                                       expected_pat_t in
                                   let g1 =
                                     FStar_TypeChecker_Rel.conj_guard g g' in
                                   let uu____7871 =
                                     let env12 =
                                       FStar_TypeChecker_Env.set_range env11
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let g2 =
                                       let uu___116_7874 = g1 in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___116_7874.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___116_7874.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___116_7874.FStar_TypeChecker_Env.implicits)
                                       } in
                                     let uu____7875 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env12 g2 in
                                     FStar_All.pipe_right uu____7875
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env11 exp1 in
                                   let uvars_to_string uvs =
                                     let uu____7887 =
                                       let uu____7889 =
                                         FStar_All.pipe_right uvs
                                           FStar_Util.set_elements in
                                       FStar_All.pipe_right uu____7889
                                         (FStar_List.map
                                            (fun uu____7907  ->
                                               match uu____7907 with
                                               | (u,uu____7911) ->
                                                   FStar_Syntax_Print.uvar_to_string
                                                     u)) in
                                     FStar_All.pipe_right uu____7887
                                       (FStar_String.concat ", ") in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____7922 =
                                       let uu____7923 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____7923 in
                                     if uu____7922
                                     then
                                       let unresolved =
                                         let uu____7930 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____7930
                                           FStar_Util.set_elements in
                                       let uu____7944 =
                                         let uu____7945 =
                                           let uu____7948 =
                                             let uu____7949 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____7950 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____7951 =
                                               let uu____7952 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____7960  ->
                                                         match uu____7960
                                                         with
                                                         | (u,uu____7964) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____7952
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____7949 uu____7950
                                               uu____7951 in
                                           (uu____7948,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____7945 in
                                       raise uu____7944
                                     else ());
                                    (let uu____7968 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____7968
                                     then
                                       let uu____7969 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____7969
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____7977 =
                   let uu____7981 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____7981
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____7977 with
                  | (scrutinee_env,uu____7994) ->
                      let uu____7997 = tc_pat true pat_t pattern in
                      (match uu____7997 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____8019 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____8034 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____8034
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____8042 =
                                      let uu____8046 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____8046 e in
                                    match uu____8042 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____8019 with
                            | (when_clause1,g_when) ->
                                let uu____8066 = tc_term pat_env branch_exp in
                                (match uu____8066 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____8085 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_31  -> Some _0_31)
                                             uu____8085 in
                                     let uu____8087 =
                                       let eqs =
                                         let uu____8093 =
                                           let uu____8094 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____8094 in
                                         if uu____8093
                                         then None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____8099 -> None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8108 -> None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8109 -> None
                                            | uu____8110 ->
                                                let uu____8111 =
                                                  let uu____8112 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8112 pat_t
                                                    scrutinee_tm e in
                                                Some uu____8111) in
                                       let uu____8113 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____8113 with
                                       | (c1,g_branch1) ->
                                           let uu____8123 =
                                             match (eqs, when_condition) with
                                             | uu____8130 when
                                                 let uu____8135 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8135
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____8143 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8144 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8143, uu____8144)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____8151 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8151 in
                                                 let uu____8152 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8153 =
                                                   let uu____8154 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8154 g_when in
                                                 (uu____8152, uu____8153)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____8160 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8160, g_when) in
                                           (match uu____8123 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____8168 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____8169 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8168, uu____8169,
                                                  g_branch1)) in
                                     (match uu____8087 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8182 =
                                              let uu____8183 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8183 in
                                            if uu____8182
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8214 =
                                                     let uu____8215 =
                                                       let uu____8216 =
                                                         let uu____8218 =
                                                           let uu____8222 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8222 in
                                                         snd uu____8218 in
                                                       FStar_List.length
                                                         uu____8216 in
                                                     uu____8215 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8214
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____8232 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8232 with
                                                     | None  -> []
                                                     | uu____8243 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None in
                                                         let disc1 =
                                                           let uu____8253 =
                                                             let uu____8254 =
                                                               let uu____8255
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8255] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8254 in
                                                           uu____8253 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8260 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool in
                                                         [uu____8260]
                                                   else [] in
                                                 let fail uu____8268 =
                                                   let uu____8269 =
                                                     let uu____8270 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____8271 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____8272 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8270 uu____8271
                                                       uu____8272 in
                                                   failwith uu____8269 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8293) ->
                                                       head_constructor t1
                                                   | uu____8299 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____8302 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____8302
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____8304 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____8313;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8314;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8315;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8316;_},uu____8317)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8340 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____8342 =
                                                       let uu____8343 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8343
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____8342]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8344 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8354 =
                                                       let uu____8355 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8355 in
                                                     if uu____8354
                                                     then []
                                                     else
                                                       (let uu____8362 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8362)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8368 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8374 =
                                                       let uu____8375 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8375 in
                                                     if uu____8374
                                                     then []
                                                     else
                                                       (let uu____8382 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8382)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8409 =
                                                       let uu____8410 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8410 in
                                                     if uu____8409
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8419 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8435
                                                                     ->
                                                                    match uu____8435
                                                                    with
                                                                    | 
                                                                    (ei,uu____8442)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8452
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8452
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8463
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8472
                                                                    =
                                                                    let uu____8473
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None in
                                                                    let uu____8478
                                                                    =
                                                                    let uu____8479
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8479] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8473
                                                                    uu____8478 in
                                                                    uu____8472
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8419
                                                            FStar_List.flatten in
                                                        let uu____8491 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8491
                                                          sub_term_guards)
                                                 | uu____8495 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8507 =
                                                   let uu____8508 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8508 in
                                                 if uu____8507
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8511 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8511 in
                                                    let uu____8514 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8514 with
                                                    | (k,uu____8518) ->
                                                        let uu____8519 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8519
                                                         with
                                                         | (t1,uu____8524,uu____8525)
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
                                          ((let uu____8531 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8531
                                            then
                                              let uu____8532 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8532
                                            else ());
                                           (let uu____8534 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8534, branch_guard, c1,
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
          let uu____8552 = check_let_bound_def true env1 lb in
          (match uu____8552 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8566 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____8575 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____8575, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8578 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8578
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8580 =
                      let uu____8585 =
                        let uu____8591 =
                          let uu____8596 =
                            let uu____8604 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8604) in
                          [uu____8596] in
                        FStar_TypeChecker_Util.generalize env1 uu____8591 in
                      FStar_List.hd uu____8585 in
                    match uu____8580 with
                    | (uu____8633,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8566 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8644 =
                      let uu____8649 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8649
                      then
                        let uu____8654 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8654 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8671 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____8671
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8672 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos in
                                 (uu____8672, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8690 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8690
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8698 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8698
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____8644 with
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
                           let uu____8730 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8730,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8749 -> failwith "Impossible"
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
            let uu___117_8770 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___117_8770.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___117_8770.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___117_8770.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___117_8770.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___117_8770.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___117_8770.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___117_8770.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___117_8770.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___117_8770.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___117_8770.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___117_8770.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___117_8770.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___117_8770.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___117_8770.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___117_8770.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___117_8770.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___117_8770.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___117_8770.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___117_8770.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___117_8770.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___117_8770.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___117_8770.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___117_8770.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___117_8770.FStar_TypeChecker_Env.proof_ns)
            } in
          let uu____8771 =
            let uu____8777 =
              let uu____8778 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8778 FStar_Pervasives.fst in
            check_let_bound_def false uu____8777 lb in
          (match uu____8771 with
           | (e1,uu____8790,c1,g1,annotated) ->
               let x =
                 let uu___118_8795 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___118_8795.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___118_8795.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8796 =
                 let uu____8799 =
                   let uu____8800 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8800] in
                 FStar_Syntax_Subst.open_term uu____8799 e2 in
               (match uu____8796 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = fst xbinder in
                    let uu____8812 =
                      let uu____8816 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8816 e21 in
                    (match uu____8812 with
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
                           let uu____8831 =
                             let uu____8834 =
                               let uu____8835 =
                                 let uu____8843 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8843) in
                               FStar_Syntax_Syntax.Tm_let uu____8835 in
                             FStar_Syntax_Syntax.mk uu____8834 in
                           uu____8831
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____8858 =
                             let uu____8859 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____8860 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____8859
                               c1.FStar_Syntax_Syntax.res_typ uu____8860 e11 in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8858 in
                         let g21 =
                           let uu____8862 =
                             let uu____8863 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____8863 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____8862 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____8865 =
                           let uu____8866 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____8866 in
                         if uu____8865
                         then
                           let tt =
                             let uu____8872 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____8872 FStar_Option.get in
                           ((let uu____8876 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8876
                             then
                               let uu____8877 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____8878 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____8877 uu____8878
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____8883 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8883
                             then
                               let uu____8884 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____8885 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8884 uu____8885
                             else ());
                            (e4,
                              ((let uu___119_8887 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___119_8887.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___119_8887.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___119_8887.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8888 -> failwith "Impossible"
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
          let uu____8909 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8909 with
           | (lbs1,e21) ->
               let uu____8920 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8920 with
                | (env0,topt) ->
                    let uu____8931 = build_let_rec_env true env0 lbs1 in
                    (match uu____8931 with
                     | (lbs2,rec_env) ->
                         let uu____8942 = check_let_recs rec_env lbs2 in
                         (match uu____8942 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8954 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____8954
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____8958 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____8958
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
                                     let uu____8983 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____9005 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____9005))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8983 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____9025  ->
                                           match uu____9025 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____9050 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____9050 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____9059 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____9059 with
                                | (lbs5,e22) ->
                                    let uu____9070 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____9085 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env1 g_lbs1 in
                                    (uu____9070, cres, uu____9085)))))))
      | uu____9088 -> failwith "Impossible"
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
          let uu____9109 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9109 with
           | (lbs1,e21) ->
               let uu____9120 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9120 with
                | (env0,topt) ->
                    let uu____9131 = build_let_rec_env false env0 lbs1 in
                    (match uu____9131 with
                     | (lbs2,rec_env) ->
                         let uu____9142 = check_let_recs rec_env lbs2 in
                         (match uu____9142 with
                          | (lbs3,g_lbs) ->
                              let uu____9153 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___120_9164 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___120_9164.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___120_9164.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___121_9166 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___121_9166.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___121_9166.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___121_9166.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___121_9166.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____9153 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____9183 = tc_term env2 e21 in
                                   (match uu____9183 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9194 =
                                            let uu____9195 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9195 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9194 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___122_9199 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___122_9199.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___122_9199.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___122_9199.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9200 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9200 with
                                         | (lbs5,e23) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | Some uu____9229 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres in
                                                  let cres3 =
                                                    let uu___123_9234 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___123_9234.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___123_9234.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___123_9234.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9237 -> failwith "Impossible"
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
          let uu____9260 =
            let uu____9263 =
              let uu____9264 = FStar_Syntax_Subst.compress t in
              uu____9264.FStar_Syntax_Syntax.n in
            let uu____9267 =
              let uu____9268 = FStar_Syntax_Subst.compress lbdef in
              uu____9268.FStar_Syntax_Syntax.n in
            (uu____9263, uu____9267) in
          match uu____9260 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9274,uu____9275)) ->
              let actuals1 =
                let uu____9309 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9309
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____9334 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9334) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____9352 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____9352) in
                  let msg =
                    let uu____9360 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____9361 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9360 uu____9361 formals_msg actuals_msg in
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____9366 ->
              let uu____9369 =
                let uu____9370 =
                  let uu____9373 =
                    let uu____9374 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____9375 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9374 uu____9375 in
                  (uu____9373, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____9370 in
              raise uu____9369 in
        let uu____9376 =
          FStar_List.fold_left
            (fun uu____9383  ->
               fun lb  ->
                 match uu____9383 with
                 | (lbs1,env1) ->
                     let uu____9395 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9395 with
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
                              (let uu____9409 =
                                 let uu____9413 =
                                   let uu____9414 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left FStar_Pervasives.fst
                                     uu____9414 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___124_9419 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___124_9419.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___124_9419.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___124_9419.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___124_9419.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___124_9419.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___124_9419.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___124_9419.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___124_9419.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___124_9419.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___124_9419.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___124_9419.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___124_9419.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___124_9419.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___124_9419.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___124_9419.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___124_9419.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___124_9419.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___124_9419.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___124_9419.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___124_9419.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___124_9419.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___124_9419.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___124_9419.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___124_9419.FStar_TypeChecker_Env.proof_ns)
                                    }) t uu____9413 in
                               match uu____9409 with
                               | (t1,uu____9421,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9425 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9425);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9427 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9427
                            then
                              let uu___125_9428 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___125_9428.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___125_9428.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___125_9428.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___125_9428.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___125_9428.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___125_9428.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___125_9428.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___125_9428.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___125_9428.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___125_9428.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___125_9428.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___125_9428.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___125_9428.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___125_9428.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___125_9428.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___125_9428.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___125_9428.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___125_9428.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___125_9428.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___125_9428.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___125_9428.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___125_9428.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___125_9428.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___125_9428.FStar_TypeChecker_Env.proof_ns)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___126_9438 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___126_9438.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___126_9438.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9376 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9452 =
        let uu____9457 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9469 =
                     let uu____9470 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____9470.FStar_Syntax_Syntax.n in
                   match uu____9469 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9473 -> ()
                   | uu____9488 ->
                       let uu____9489 =
                         let uu____9490 =
                           let uu____9493 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____9493) in
                         FStar_Errors.Error uu____9490 in
                       raise uu____9489);
                  (let uu____9494 =
                     let uu____9498 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____9498
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____9494 with
                   | (e,c,g) ->
                       ((let uu____9505 =
                           let uu____9506 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____9506 in
                         if uu____9505
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
        FStar_All.pipe_right uu____9457 FStar_List.unzip in
      match uu____9452 with
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
        let uu____9535 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9535 with
        | (env1,uu____9545) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9551 = check_lbtyp top_level env lb in
            (match uu____9551 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9577 =
                     tc_maybe_toplevel_term
                       (let uu___127_9581 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___127_9581.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___127_9581.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___127_9581.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___127_9581.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___127_9581.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___127_9581.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___127_9581.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___127_9581.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___127_9581.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___127_9581.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___127_9581.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___127_9581.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___127_9581.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___127_9581.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___127_9581.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___127_9581.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___127_9581.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___127_9581.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___127_9581.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___127_9581.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___127_9581.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___127_9581.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___127_9581.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___127_9581.FStar_TypeChecker_Env.proof_ns)
                        }) e11 in
                   match uu____9577 with
                   | (e12,c1,g1) ->
                       let uu____9590 =
                         let uu____9593 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9596  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9593 e12 c1 wf_annot in
                       (match uu____9590 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9606 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9606
                              then
                                let uu____9607 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9608 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9609 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9607 uu____9608 uu____9609
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
        | uu____9635 ->
            let uu____9636 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9636 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9663 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9663)
                 else
                   (let uu____9668 = FStar_Syntax_Util.type_u () in
                    match uu____9668 with
                    | (k,uu____9679) ->
                        let uu____9680 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9680 with
                         | (t2,uu____9692,g) ->
                             ((let uu____9695 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9695
                               then
                                 let uu____9696 =
                                   let uu____9697 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9697 in
                                 let uu____9698 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9696 uu____9698
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9701 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9701))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9706  ->
      match uu____9706 with
      | (x,imp) ->
          let uu____9717 = FStar_Syntax_Util.type_u () in
          (match uu____9717 with
           | (tu,u) ->
               ((let uu____9729 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9729
                 then
                   let uu____9730 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9731 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9732 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9730 uu____9731 uu____9732
                 else ());
                (let uu____9734 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9734 with
                 | (t,uu____9745,g) ->
                     let x1 =
                       ((let uu___128_9750 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___128_9750.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___128_9750.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9752 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9752
                       then
                         let uu____9753 =
                           FStar_Syntax_Print.bv_to_string (fst x1) in
                         let uu____9754 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9753 uu____9754
                       else ());
                      (let uu____9756 = push_binding env x1 in
                       (x1, uu____9756, g, u))))))
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
            let uu____9807 = tc_binder env1 b in
            (match uu____9807 with
             | (b1,env',g,u) ->
                 let uu____9830 = aux env' bs2 in
                 (match uu____9830 with
                  | (bs3,env'1,g',us) ->
                      let uu____9859 =
                        let uu____9860 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____9860 in
                      ((b1 :: bs3), env'1, uu____9859, (u :: us)))) in
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
          (fun uu____9903  ->
             fun uu____9904  ->
               match (uu____9903, uu____9904) with
               | ((t,imp),(args1,g)) ->
                   let uu____9941 = tc_term env1 t in
                   (match uu____9941 with
                    | (t1,uu____9951,g') ->
                        let uu____9953 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____9953))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9971  ->
             match uu____9971 with
             | (pats1,g) ->
                 let uu____9985 = tc_args env p in
                 (match uu____9985 with
                  | (args,g') ->
                      let uu____9993 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____9993))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____10001 = tc_maybe_toplevel_term env e in
      match uu____10001 with
      | (e1,c,g) ->
          let uu____10011 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____10011
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____10021 =
               let uu____10024 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____10024
               then
                 let uu____10027 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____10027, false)
               else
                 (let uu____10029 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____10029, true)) in
             match uu____10021 with
             | (target_comp,allow_ghost) ->
                 let uu____10035 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____10035 with
                  | Some g' ->
                      let uu____10041 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____10041)
                  | uu____10042 ->
                      if allow_ghost
                      then
                        let uu____10047 =
                          let uu____10048 =
                            let uu____10051 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____10051, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____10048 in
                        raise uu____10047
                      else
                        (let uu____10056 =
                           let uu____10057 =
                             let uu____10060 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____10060, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____10057 in
                         raise uu____10056)))
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
      let uu____10073 = tc_tot_or_gtot_term env t in
      match uu____10073 with
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
      (let uu____10093 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10093
       then
         let uu____10094 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____10094
       else ());
      (let env1 =
         let uu___129_10097 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___129_10097.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___129_10097.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___129_10097.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___129_10097.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___129_10097.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___129_10097.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___129_10097.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___129_10097.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___129_10097.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___129_10097.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___129_10097.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___129_10097.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___129_10097.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___129_10097.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___129_10097.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___129_10097.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___129_10097.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___129_10097.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___129_10097.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___129_10097.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___129_10097.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___129_10097.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___129_10097.FStar_TypeChecker_Env.proof_ns)
         } in
       let uu____10100 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10116) ->
             let uu____10117 =
               let uu____10118 =
                 let uu____10121 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____10121) in
               FStar_Errors.Error uu____10118 in
             raise uu____10117 in
       match uu____10100 with
       | (t,c,g) ->
           let uu____10131 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____10131
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10138 =
                let uu____10139 =
                  let uu____10142 =
                    let uu____10143 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10143 in
                  let uu____10144 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____10142, uu____10144) in
                FStar_Errors.Error uu____10139 in
              raise uu____10138))
let level_of_type_fail env e t =
  let uu____10165 =
    let uu____10166 =
      let uu____10169 =
        let uu____10170 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10170 t in
      let uu____10171 = FStar_TypeChecker_Env.get_range env in
      (uu____10169, uu____10171) in
    FStar_Errors.Error uu____10166 in
  raise uu____10165
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____10188 =
            let uu____10189 = FStar_Syntax_Util.unrefine t1 in
            uu____10189.FStar_Syntax_Syntax.n in
          match uu____10188 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10193 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____10196 = FStar_Syntax_Util.type_u () in
                 match uu____10196 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___132_10202 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___132_10202.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___132_10202.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___132_10202.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___132_10202.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___132_10202.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___132_10202.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___132_10202.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___132_10202.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___132_10202.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___132_10202.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___132_10202.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___132_10202.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___132_10202.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___132_10202.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___132_10202.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___132_10202.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___132_10202.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___132_10202.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___132_10202.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___132_10202.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___132_10202.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___132_10202.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___132_10202.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___132_10202.FStar_TypeChecker_Env.proof_ns)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____10206 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____10206
                       | uu____10207 ->
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
      let uu____10216 =
        let uu____10217 = FStar_Syntax_Subst.compress e in
        uu____10217.FStar_Syntax_Syntax.n in
      match uu____10216 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10222 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10227 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10250 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10261) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10286,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10301) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10308 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10308 with | ((uu____10319,t),uu____10321) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10324,(FStar_Util.Inl t,uu____10326),uu____10327) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10363,(FStar_Util.Inr c,uu____10365),uu____10366) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)) None
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10409;
             FStar_Syntax_Syntax.pos = uu____10410;
             FStar_Syntax_Syntax.vars = uu____10411;_},us)
          ->
          let uu____10417 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10417 with
           | ((us',t),uu____10430) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10442 =
                     let uu____10443 =
                       let uu____10446 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10446) in
                     FStar_Errors.Error uu____10443 in
                   raise uu____10442)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10453 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10454 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10462) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10479 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10479 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10490  ->
                      match uu____10490 with
                      | (b,uu____10494) ->
                          let uu____10495 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10495) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10500 = universe_of_aux env res in
                 level_of_type env res uu____10500 in
               let u_c =
                 let uu____10502 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10502 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10505 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10505 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____10575 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10585 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10615 ->
                let uu____10616 = universe_of_aux env hd3 in
                (uu____10616, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10626 ->
                let uu____10627 = universe_of_aux env hd3 in
                (uu____10627, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10637 ->
                let uu____10646 = universe_of_aux env hd3 in
                (uu____10646, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10656 ->
                let uu____10661 = universe_of_aux env hd3 in
                (uu____10661, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10671 ->
                let uu____10689 = universe_of_aux env hd3 in
                (uu____10689, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10699 ->
                let uu____10704 = universe_of_aux env hd3 in
                (uu____10704, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10714 ->
                let uu____10715 = universe_of_aux env hd3 in
                (uu____10715, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10725 ->
                let uu____10733 = universe_of_aux env hd3 in
                (uu____10733, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____10743 ->
                let uu____10748 = universe_of_aux env hd3 in
                (uu____10748, args1)
            | FStar_Syntax_Syntax.Tm_type uu____10758 ->
                let uu____10759 = universe_of_aux env hd3 in
                (uu____10759, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10769,hd4::uu____10771) ->
                let uu____10818 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____10818 with
                 | (uu____10828,uu____10829,hd5) ->
                     let uu____10845 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____10845 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10880 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____10882 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____10882 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10917 ->
                let uu____10918 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____10918 with
                 | (env1,uu____10932) ->
                     let env2 =
                       let uu___133_10936 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___133_10936.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___133_10936.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___133_10936.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___133_10936.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___133_10936.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___133_10936.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___133_10936.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___133_10936.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___133_10936.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___133_10936.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___133_10936.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___133_10936.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___133_10936.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___133_10936.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___133_10936.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___133_10936.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___133_10936.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___133_10936.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___133_10936.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___133_10936.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___133_10936.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___133_10936.FStar_TypeChecker_Env.proof_ns)
                       } in
                     ((let uu____10938 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____10938
                       then
                         let uu____10939 =
                           let uu____10940 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____10940 in
                         let uu____10941 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10939 uu____10941
                       else ());
                      (let uu____10943 = tc_term env2 hd3 in
                       match uu____10943 with
                       | (uu____10956,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10957;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10959;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10960;_},g)
                           ->
                           ((let uu____10970 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____10970
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____10978 = type_of_head true hd1 args in
          (match uu____10978 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____11007 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____11007 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____11044 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____11044)))
      | FStar_Syntax_Syntax.Tm_match (uu____11047,hd1::uu____11049) ->
          let uu____11096 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____11096 with
           | (uu____11099,uu____11100,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11116,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____11150 = universe_of_aux env e in
      level_of_type env e uu____11150
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____11163 = tc_binders env tps in
      match uu____11163 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))