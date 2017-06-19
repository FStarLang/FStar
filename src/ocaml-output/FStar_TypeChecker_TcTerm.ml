open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___88_5 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___88_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___88_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___88_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___88_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___88_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___88_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___88_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___88_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___88_5.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___88_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___88_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___88_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___88_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___88_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___88_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___88_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___88_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___88_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___88_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___88_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___88_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___88_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___88_5.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___88_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___88_5.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___88_5.FStar_TypeChecker_Env.is_native_tactic)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___89_10 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___89_10.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___89_10.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___89_10.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___89_10.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___89_10.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___89_10.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___89_10.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___89_10.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___89_10.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___89_10.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___89_10.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___89_10.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___89_10.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___89_10.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___89_10.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___89_10.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___89_10.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___89_10.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___89_10.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___89_10.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___89_10.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___89_10.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___89_10.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___89_10.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___89_10.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___89_10.FStar_TypeChecker_Env.is_native_tactic)
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
           let uu____37 =
             let uu____38 =
               let uu____39 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____40 =
                 let uu____42 = FStar_Syntax_Syntax.as_arg tl1 in [uu____42] in
               uu____39 :: uu____40 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____38 in
           uu____37 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)
      vs FStar_Syntax_Util.lex_top
let is_eq: FStar_Syntax_Syntax.arg_qualifier option -> Prims.bool =
  fun uu___83_51  ->
    match uu___83_51 with
    | Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____53 -> false
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
            | uu____108 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____114 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____114 with
                 | None  -> t1
                 | Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____122 =
                          let msg =
                            match head_opt with
                            | None  ->
                                let uu____124 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____124
                            | Some head1 ->
                                let uu____126 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____127 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____126 uu____127 in
                          let uu____128 =
                            let uu____129 =
                              let uu____132 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____132) in
                            FStar_Errors.Error uu____129 in
                          raise uu____128 in
                        let s =
                          let uu____134 =
                            let uu____135 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives.fst
                              uu____135 in
                          FStar_TypeChecker_Util.new_uvar env uu____134 in
                        let uu____140 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____140 with
                        | Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____144 -> fail ())) in
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
        let uu____181 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____181 then s else (FStar_Syntax_Syntax.NT ((fst b), v1)) :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___90_197 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___90_197.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___90_197.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____198  ->
             let uu____199 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____199 t)
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
            let uu____244 =
              let uu____245 = FStar_Syntax_Subst.compress t in
              uu____245.FStar_Syntax_Syntax.n in
            match uu____244 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____248,c) ->
                let uu____260 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____260
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____262 =
                    let uu____263 = FStar_Syntax_Subst.compress t1 in
                    uu____263.FStar_Syntax_Syntax.n in
                  (match uu____262 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____267 -> false
                   | uu____268 -> true)
                else false
            | uu____270 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____273 =
                  let uu____276 =
                    (let uu____277 = should_return t in
                     Prims.op_Negation uu____277) ||
                      (let uu____278 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____278) in
                  if uu____276
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____273
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____286 =
            let uu____290 = FStar_TypeChecker_Env.expected_typ env in
            match uu____290 with
            | None  -> let uu____295 = memo_tk e t in (uu____295, lc, guard)
            | Some t' ->
                ((let uu____298 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____298
                  then
                    let uu____299 = FStar_Syntax_Print.term_to_string t in
                    let uu____300 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____299
                      uu____300
                  else ());
                 (let uu____302 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____302 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____313 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____313 with
                       | (e2,g) ->
                           ((let uu____322 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____322
                             then
                               let uu____323 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____324 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____325 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____326 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____323 uu____324 uu____325 uu____326
                             else ());
                            (let msg =
                               let uu____332 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____332
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_39  -> Some _0_39)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____347 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____347 with
                             | (lc2,g2) ->
                                 let uu____355 = memo_tk e2 t' in
                                 (uu____355, (set_lcomp_result lc2 t'), g2)))))) in
          match uu____286 with
          | (e1,lc1,g) ->
              ((let uu____363 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____363
                then
                  let uu____364 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____364
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
        let uu____384 = FStar_TypeChecker_Env.expected_typ env in
        match uu____384 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____390 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____390 with
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
      fun uu____415  ->
        match uu____415 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____435 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____435
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____437 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____437
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____439 =
              match copt with
              | Some uu____446 -> (copt, c)
              | None  ->
                  let uu____448 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Syntax_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____449 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____449)) in
                  if uu____448
                  then
                    let uu____453 =
                      let uu____455 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      Some uu____455 in
                    (uu____453, c)
                  else
                    (let uu____458 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____458
                     then let uu____462 = tot_or_gtot c in (None, uu____462)
                     else
                       (let uu____465 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____465
                        then
                          let uu____469 =
                            let uu____471 = tot_or_gtot c in Some uu____471 in
                          (uu____469, c)
                        else (None, c))) in
            (match uu____439 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | None  -> (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | Some expected_c ->
                      let uu____487 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____487 with
                       | (e1,uu____495,g) ->
                           let g1 =
                             let uu____498 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____498
                               "could not prove post-condition" g in
                           ((let uu____500 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____500
                             then
                               let uu____501 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____502 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____501 uu____502
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard env uu____528 =
  match uu____528 with
  | (te,kt,f) ->
      let uu____535 = FStar_TypeChecker_Rel.guard_form f in
      (match uu____535 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____540 =
             let uu____541 =
               let uu____544 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____545 = FStar_TypeChecker_Env.get_range env in
               (uu____544, uu____545) in
             FStar_Errors.Error uu____541 in
           raise uu____540)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____553 = FStar_TypeChecker_Env.expected_typ env in
    match uu____553 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____556 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____556
let check_smt_pat env t bs c =
  let uu____597 = FStar_Syntax_Util.is_smt_lemma t in
  if uu____597
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____598;
          FStar_Syntax_Syntax.effect_name = uu____599;
          FStar_Syntax_Syntax.result_typ = uu____600;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____604)::[];
          FStar_Syntax_Syntax.flags = uu____605;_}
        ->
        let pat_vars =
          let uu____639 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats in
          FStar_Syntax_Free.names uu____639 in
        let uu____640 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____652  ->
                  match uu____652 with
                  | (b,uu____656) ->
                      let uu____657 = FStar_Util.set_mem b pat_vars in
                      Prims.op_Negation uu____657)) in
        (match uu____640 with
         | None  -> ()
         | Some (x,uu____661) ->
             let uu____664 =
               let uu____665 = FStar_Syntax_Print.bv_to_string x in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____665 in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____664)
    | uu____666 -> failwith "Impossible"
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
        let uu____690 =
          let uu____691 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____691 in
        if uu____690
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___91_709 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___91_709.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___91_709.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___91_709.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___91_709.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___91_709.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___91_709.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___91_709.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___91_709.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___91_709.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___91_709.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___91_709.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___91_709.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___91_709.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___91_709.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___91_709.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___91_709.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___91_709.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___91_709.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___91_709.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___91_709.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___91_709.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___91_709.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___91_709.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___91_709.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___91_709.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___91_709.FStar_TypeChecker_Env.is_native_tactic)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____732  ->
                           match uu____732 with
                           | (b,uu____737) ->
                               let t =
                                 let uu____739 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____739 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____741 -> []
                                | FStar_Syntax_Syntax.Tm_arrow uu____742 ->
                                    []
                                | uu____750 ->
                                    let uu____751 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____751]))) in
                 let as_lex_list dec =
                   let uu____756 = FStar_Syntax_Util.head_and_args dec in
                   match uu____756 with
                   | (head1,uu____767) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____783 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____786 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___84_790  ->
                           match uu___84_790 with
                           | FStar_Syntax_Syntax.DECREASES uu____791 -> true
                           | uu____794 -> false)) in
                 match uu____786 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____798 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____804 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____816 =
                 match uu____816 with
                 | (l,t) ->
                     let uu____825 =
                       let uu____826 = FStar_Syntax_Subst.compress t in
                       uu____826.FStar_Syntax_Syntax.n in
                     (match uu____825 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____859  ->
                                    match uu____859 with
                                    | (x,imp) ->
                                        let uu____866 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____866
                                        then
                                          let uu____869 =
                                            let uu____870 =
                                              let uu____872 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              Some uu____872 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____870
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____869, imp)
                                        else (x, imp))) in
                          let uu____874 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____874 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____887 =
                                   let uu____888 =
                                     let uu____889 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____890 =
                                       let uu____892 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____892] in
                                     uu____889 :: uu____890 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____888 in
                                 uu____887 None r in
                               let uu____897 = FStar_Util.prefix formals2 in
                               (match uu____897 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___92_923 = last1 in
                                      let uu____924 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___92_923.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___92_923.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____924
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____941 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____941
                                      then
                                        let uu____942 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____943 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____944 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____942 uu____943 uu____944
                                      else ());
                                     (l, t'))))
                      | uu____948 ->
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
        (let uu___93_1231 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___93_1231.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___93_1231.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___93_1231.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___93_1231.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___93_1231.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___93_1231.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___93_1231.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___93_1231.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___93_1231.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___93_1231.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___93_1231.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___93_1231.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___93_1231.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___93_1231.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___93_1231.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___93_1231.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___93_1231.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___93_1231.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___93_1231.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___93_1231.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___93_1231.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___93_1231.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___93_1231.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___93_1231.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___93_1231.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___93_1231.FStar_TypeChecker_Env.is_native_tactic)
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
      (let uu____1240 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1240
       then
         let uu____1241 =
           let uu____1242 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1242 in
         let uu____1243 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1241 uu____1243
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1249 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1273 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1278 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1287 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1288 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1289 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1290 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1291 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1306 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1314 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1319 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1325 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1325 with
            | (e2,c,g) ->
                let g1 =
                  let uu___94_1336 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___94_1336.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___94_1336.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___94_1336.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1349 = FStar_Syntax_Util.type_u () in
           (match uu____1349 with
            | (t,u) ->
                let uu____1357 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1357 with
                 | (e2,c,g) ->
                     let uu____1367 =
                       let uu____1376 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1376 with
                       | (env2,uu____1389) -> tc_pats env2 pats in
                     (match uu____1367 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___95_1410 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___95_1410.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___95_1410.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___95_1410.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1411 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1422 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1411, c, uu____1422))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1430 =
             let uu____1431 = FStar_Syntax_Subst.compress e1 in
             uu____1431.FStar_Syntax_Syntax.n in
           (match uu____1430 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1437,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1439;
                               FStar_Syntax_Syntax.lbtyp = uu____1440;
                               FStar_Syntax_Syntax.lbeff = uu____1441;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1459 =
                  let uu____1463 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1463 e11 in
                (match uu____1459 with
                 | (e12,c1,g1) ->
                     let uu____1470 = tc_term env1 e2 in
                     (match uu____1470 with
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
                            let uu____1487 =
                              let uu____1490 =
                                let uu____1491 =
                                  let uu____1499 =
                                    let uu____1503 =
                                      let uu____1505 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1505] in
                                    (false, uu____1503) in
                                  (uu____1499, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1491 in
                              FStar_Syntax_Syntax.mk uu____1490 in
                            uu____1487
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
                          let uu____1535 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1535)))
            | uu____1538 ->
                let uu____1539 = tc_term env1 e1 in
                (match uu____1539 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1563) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1578 = tc_term env1 e1 in
           (match uu____1578 with
            | (e2,c,g) ->
                let e3 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1604) ->
           let uu____1640 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1640 with
            | (env0,uu____1648) ->
                let uu____1651 = tc_comp env0 expected_c in
                (match uu____1651 with
                 | (expected_c1,uu____1659,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1664 =
                       let uu____1668 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1668 e1 in
                     (match uu____1664 with
                      | (e2,c',g') ->
                          let uu____1675 =
                            let uu____1679 =
                              let uu____1682 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____1682) in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1679 in
                          (match uu____1675 with
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
                                 let uu____1733 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1733 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | None  -> f
                                 | Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic) in
                               let uu____1738 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1738 with
                                | (e5,c,f2) ->
                                    let uu____1748 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____1748))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1752) ->
           let uu____1788 = FStar_Syntax_Util.type_u () in
           (match uu____1788 with
            | (k,u) ->
                let uu____1796 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1796 with
                 | (t1,uu____1804,f) ->
                     let uu____1806 =
                       let uu____1810 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1810 e1 in
                     (match uu____1806 with
                      | (e2,c,g) ->
                          let uu____1817 =
                            let uu____1820 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1823  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1820 e2 c f in
                          (match uu____1817 with
                           | (c1,f1) ->
                               let uu____1829 =
                                 let uu____1833 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, ((FStar_Util.Inl t1), None),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____1833 c1 in
                               (match uu____1829 with
                                | (e3,c2,f2) ->
                                    let uu____1869 =
                                      let uu____1870 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1870 in
                                    (e3, c2, uu____1869))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1871;
              FStar_Syntax_Syntax.pos = uu____1872;
              FStar_Syntax_Syntax.vars = uu____1873;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1917 = FStar_Syntax_Util.head_and_args top in
           (match uu____1917 with
            | (unary_op,uu____1931) ->
                let head1 =
                  let uu____1949 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1949 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____1993);
              FStar_Syntax_Syntax.tk = uu____1994;
              FStar_Syntax_Syntax.pos = uu____1995;
              FStar_Syntax_Syntax.vars = uu____1996;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2040 = FStar_Syntax_Util.head_and_args top in
           (match uu____2040 with
            | (unary_op,uu____2054) ->
                let head1 =
                  let uu____2072 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____2072 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____2116;
              FStar_Syntax_Syntax.pos = uu____2117;
              FStar_Syntax_Syntax.vars = uu____2118;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2144 =
               let uu____2148 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____2148 with | (env0,uu____2156) -> tc_term env0 e1 in
             match uu____2144 with
             | (e2,c,g) ->
                 let uu____2165 = FStar_Syntax_Util.head_and_args top in
                 (match uu____2165 with
                  | (reify_op,uu____2179) ->
                      let u_c =
                        let uu____2195 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____2195 with
                        | (uu____2199,c',uu____2201) ->
                            let uu____2202 =
                              let uu____2203 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____2203.FStar_Syntax_Syntax.n in
                            (match uu____2202 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2207 ->
                                 let uu____2208 = FStar_Syntax_Util.type_u () in
                                 (match uu____2208 with
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
                                            let uu____2217 =
                                              let uu____2218 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2219 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2220 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2218 uu____2219
                                                uu____2220 in
                                            failwith uu____2217);
                                       u))) in
                      let repr =
                        let uu____2222 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2222 u_c in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2244 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2244
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2245 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2245 with
                       | (e4,c2,g') ->
                           let uu____2255 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2255)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2257;
              FStar_Syntax_Syntax.pos = uu____2258;
              FStar_Syntax_Syntax.vars = uu____2259;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2291 =
               let uu____2292 =
                 let uu____2293 =
                   let uu____2296 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2296, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2293 in
               raise uu____2292 in
             let uu____2300 = FStar_Syntax_Util.head_and_args top in
             match uu____2300 with
             | (reflect_op,uu____2314) ->
                 let uu____2329 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2329 with
                  | None  -> no_reflect ()
                  | Some (ed,qualifiers) ->
                      let uu____2347 =
                        let uu____2348 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2348 in
                      if uu____2347
                      then no_reflect ()
                      else
                        (let uu____2354 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2354 with
                         | (env_no_ex,topt) ->
                             let uu____2365 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2380 =
                                   let uu____2383 =
                                     let uu____2384 =
                                       let uu____2394 =
                                         let uu____2396 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2397 =
                                           let uu____2399 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2399] in
                                         uu____2396 :: uu____2397 in
                                       (repr, uu____2394) in
                                     FStar_Syntax_Syntax.Tm_app uu____2384 in
                                   FStar_Syntax_Syntax.mk uu____2383 in
                                 uu____2380 None top.FStar_Syntax_Syntax.pos in
                               let uu____2409 =
                                 let uu____2413 =
                                   let uu____2414 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2414
                                     FStar_Pervasives.fst in
                                 tc_tot_or_gtot_term uu____2413 t in
                               match uu____2409 with
                               | (t1,uu____2431,g) ->
                                   let uu____2433 =
                                     let uu____2434 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2434.FStar_Syntax_Syntax.n in
                                   (match uu____2433 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2445,(res,uu____2447)::
                                         (wp,uu____2449)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2483 -> failwith "Impossible") in
                             (match uu____2365 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2507 =
                                    let uu____2510 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2510 with
                                    | (e2,c,g) ->
                                        ((let uu____2520 =
                                            let uu____2521 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2521 in
                                          if uu____2520
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2527 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2527 with
                                          | None  ->
                                              ((let uu____2532 =
                                                  let uu____2536 =
                                                    let uu____2539 =
                                                      let uu____2540 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2541 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2540 uu____2541 in
                                                    (uu____2539,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2536] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2532);
                                               (let uu____2546 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2546)))
                                          | Some g' ->
                                              let uu____2548 =
                                                let uu____2549 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2549 in
                                              (e2, uu____2548))) in
                                  (match uu____2507 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2556 =
                                           let uu____2557 =
                                             let uu____2558 =
                                               let uu____2559 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2559] in
                                             let uu____2560 =
                                               let uu____2566 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2566] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2558;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2560;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2557 in
                                         FStar_All.pipe_right uu____2556
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e2, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2587 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2587 with
                                        | (e4,c1,g') ->
                                            let uu____2597 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2597))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,(tau,uu____2600)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           (match env1.FStar_TypeChecker_Env.expected_typ with
            | Some typ -> tc_synth env1 typ tau
            | None  ->
                let uu____2626 =
                  let uu____2627 =
                    let uu____2630 = FStar_TypeChecker_Env.get_range env1 in
                    ("synth_by_tactic: need a type annotation when no expected type is present",
                      uu____2630) in
                  FStar_Errors.Error uu____2627 in
                raise uu____2626)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(a,uu____2636)::(tau,uu____2638)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 -> tc_synth env1 a tau
       | FStar_Syntax_Syntax.Tm_app
           (head1,(a,uu____2670)::uu____2671::(tau,uu____2673)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 -> tc_synth env1 a tau
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2729 =
               let uu____2730 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2730 FStar_Pervasives.fst in
             FStar_All.pipe_right uu____2729 instantiate_both in
           ((let uu____2739 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2739
             then
               let uu____2740 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2741 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2740
                 uu____2741
             else ());
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.quote_lid
                   -> true
               | uu____2745 -> false in
             let uu____2746 = tc_term (no_inst env2) head1 in
             match uu____2746 with
             | (head2,chead,g_head) ->
                 let uu____2756 =
                   let uu____2760 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2760
                   then
                     let uu____2764 =
                       let uu____2768 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____2768 in
                     match uu____2764 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____2777 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____2778 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____2778))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____2777
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____2783 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____2783) in
                 (match uu____2756 with
                  | (e1,c,g) ->
                      ((let uu____2792 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2792
                        then
                          let uu____2793 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2793
                        else ());
                       (let uu____2795 = comp_check_expected_typ env0 e1 c in
                        match uu____2795 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____2806 =
                                let uu____2807 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2807.FStar_Syntax_Syntax.n in
                              match uu____2806 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2811) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___96_2843 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___96_2843.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___96_2843.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___96_2843.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2868 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2870 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2870 in
                            ((let uu____2872 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2872
                              then
                                let uu____2873 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2874 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2873 uu____2874
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2904 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2904 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2916 = tc_term env12 e1 in
                (match uu____2916 with
                 | (e11,c1,g1) ->
                     let uu____2926 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2932 = FStar_Syntax_Util.type_u () in
                           (match uu____2932 with
                            | (k,uu____2938) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2940 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2940, res_t)) in
                     (match uu____2926 with
                      | (env_branches,res_t) ->
                          ((let uu____2947 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2947
                            then
                              let uu____2948 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2948
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2999 =
                              let uu____3002 =
                                FStar_List.fold_right
                                  (fun uu____3021  ->
                                     fun uu____3022  ->
                                       match (uu____3021, uu____3022) with
                                       | ((uu____3054,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____3087 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____3087))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____3002 with
                              | (cases,g) ->
                                  let uu____3108 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____3108, g) in
                            match uu____2999 with
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
                                           (fun uu____3161  ->
                                              match uu____3161 with
                                              | ((pat,wopt,br),uu____3177,lc,uu____3179)
                                                  ->
                                                  let uu____3186 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____3186))) in
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
                                  let uu____3242 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____3242
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____3249 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____3249 in
                                     let lb =
                                       let uu____3253 =
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
                                           uu____3253;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____3257 =
                                         let uu____3260 =
                                           let uu____3261 =
                                             let uu____3269 =
                                               let uu____3270 =
                                                 let uu____3271 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____3271] in
                                               FStar_Syntax_Subst.close
                                                 uu____3270 e_match in
                                             ((false, [lb]), uu____3269) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____3261 in
                                         FStar_Syntax_Syntax.mk uu____3260 in
                                       uu____3257
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____3285 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____3285
                                  then
                                    let uu____3286 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____3287 =
                                      let uu____3288 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____3288 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____3286 uu____3287
                                  else ());
                                 (let uu____3290 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____3290))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3293;
                FStar_Syntax_Syntax.lbunivs = uu____3294;
                FStar_Syntax_Syntax.lbtyp = uu____3295;
                FStar_Syntax_Syntax.lbeff = uu____3296;
                FStar_Syntax_Syntax.lbdef = uu____3297;_}::[]),uu____3298)
           ->
           ((let uu____3313 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3313
             then
               let uu____3314 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3314
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____3316),uu____3317) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3327;
                FStar_Syntax_Syntax.lbunivs = uu____3328;
                FStar_Syntax_Syntax.lbtyp = uu____3329;
                FStar_Syntax_Syntax.lbeff = uu____3330;
                FStar_Syntax_Syntax.lbdef = uu____3331;_}::uu____3332),uu____3333)
           ->
           ((let uu____3349 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3349
             then
               let uu____3350 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3350
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3352),uu____3353) ->
           check_inner_let_rec env1 top)
and tc_synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let uu____3368 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____3368 with
        | (env',uu____3376) ->
            let uu____3379 = tc_term env' typ in
            (match uu____3379 with
             | (typ1,uu____3387,g1) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                  (let uu____3390 = tc_term env' tau in
                   match uu____3390 with
                   | (tau1,c,g2) ->
                       (FStar_TypeChecker_Rel.force_trivial_guard env' g2;
                        (let uu____3402 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "Tac") in
                         if uu____3402
                         then
                           let uu____3403 =
                             FStar_Syntax_Print.term_to_string tau1 in
                           let uu____3404 =
                             FStar_Syntax_Print.term_to_string typ1 in
                           FStar_Util.print2
                             "Running tactic %s at return type %s\n"
                             uu____3403 uu____3404
                         else ());
                        (let t =
                           env.FStar_TypeChecker_Env.synth env' typ1 tau1 in
                         (let uu____3408 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Tac") in
                          if uu____3408
                          then
                            let uu____3409 =
                              FStar_Syntax_Print.term_to_string t in
                            FStar_Util.print1 "Got %s\n" uu____3409
                          else ());
                         FStar_TypeChecker_Util.check_uvars
                           tau1.FStar_Syntax_Syntax.pos t;
                         tc_term env t)))))
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
          let uu____3425 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3425 with
           | (tactic1,uu____3431,uu____3432) -> Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____3467 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3467 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3480 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3480
              then FStar_Util.Inl t1
              else
                (let uu____3484 =
                   let uu____3485 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3485 in
                 FStar_Util.Inr uu____3484) in
            let is_data_ctor uu___85_3494 =
              match uu___85_3494 with
              | Some (FStar_Syntax_Syntax.Data_ctor ) -> true
              | Some (FStar_Syntax_Syntax.Record_ctor uu____3496) -> true
              | uu____3500 -> false in
            let uu____3502 =
              (is_data_ctor dc) &&
                (let uu____3503 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3503) in
            if uu____3502
            then
              let uu____3509 =
                let uu____3510 =
                  let uu____3513 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3516 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3513, uu____3516) in
                FStar_Errors.Error uu____3510 in
              raise uu____3509
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3527 =
            let uu____3528 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3528 in
          failwith uu____3527
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3547 =
              let uu____3548 = FStar_Syntax_Subst.compress t1 in
              uu____3548.FStar_Syntax_Syntax.n in
            match uu____3547 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3551 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3559 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___97_3579 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___97_3579.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___97_3579.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___97_3579.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3607 =
            let uu____3614 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3614 with
            | None  ->
                let uu____3622 = FStar_Syntax_Util.type_u () in
                (match uu____3622 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3607 with
           | (t,uu____3643,g0) ->
               let uu____3651 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3651 with
                | (e1,uu____3662,g1) ->
                    let uu____3670 =
                      let uu____3671 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3671
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3672 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3670, uu____3672)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3674 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3683 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3683)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3674 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___98_3697 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___98_3697.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___98_3697.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3700 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3700 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3713 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3713
                       then FStar_Util.Inl t1
                       else
                         (let uu____3717 =
                            let uu____3718 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3718 in
                          FStar_Util.Inr uu____3717) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3724;
             FStar_Syntax_Syntax.pos = uu____3725;
             FStar_Syntax_Syntax.vars = uu____3726;_},uu____3727)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.synth_lid
          ->
          let uu____3732 =
            let uu____3733 =
              let uu____3736 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____3736) in
            FStar_Errors.Error uu____3733 in
          raise uu____3732
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.synth_lid ->
          let uu____3741 =
            let uu____3742 =
              let uu____3745 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____3745) in
            FStar_Errors.Error uu____3742 in
          raise uu____3741
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3750;
             FStar_Syntax_Syntax.pos = uu____3751;
             FStar_Syntax_Syntax.vars = uu____3752;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3760 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3760 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3786 =
                     let uu____3787 =
                       let uu____3790 =
                         let uu____3791 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____3792 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____3799 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____3791 uu____3792 uu____3799 in
                       let uu____3806 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____3790, uu____3806) in
                     FStar_Errors.Error uu____3787 in
                   raise uu____3786)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____3813 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___99_3815 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___100_3816 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___100_3816.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___100_3816.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___99_3815.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___99_3815.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3832 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3832 us1 in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3844 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3844 with
           | ((us,t),range) ->
               ((let uu____3862 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3862
                 then
                   let uu____3863 =
                     let uu____3864 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3864 in
                   let uu____3865 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3866 = FStar_Range.string_of_range range in
                   let uu____3867 = FStar_Range.string_of_use_range range in
                   let uu____3868 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
                     uu____3863 uu____3865 uu____3866 uu____3867 uu____3868
                 else ());
                (let fv' =
                   let uu___101_3871 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___102_3872 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___102_3872.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___102_3872.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___101_3871.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___101_3871.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3888 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3888 us in
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
          let uu____3924 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3924 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3933 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3933 with
                | (env2,uu____3941) ->
                    let uu____3944 = tc_binders env2 bs1 in
                    (match uu____3944 with
                     | (bs2,env3,g,us) ->
                         let uu____3956 = tc_comp env3 c1 in
                         (match uu____3956 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___103_3969 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___103_3969.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___103_3969.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___103_3969.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____3990 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3990 in
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
          let uu____4025 =
            let uu____4028 =
              let uu____4029 = FStar_Syntax_Syntax.mk_binder x in
              [uu____4029] in
            FStar_Syntax_Subst.open_term uu____4028 phi in
          (match uu____4025 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____4036 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____4036 with
                | (env2,uu____4044) ->
                    let uu____4047 =
                      let uu____4054 = FStar_List.hd x1 in
                      tc_binder env2 uu____4054 in
                    (match uu____4047 with
                     | (x2,env3,f1,u) ->
                         ((let uu____4071 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____4071
                           then
                             let uu____4072 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____4073 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____4074 =
                               FStar_Syntax_Print.bv_to_string (fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____4072 uu____4073 uu____4074
                           else ());
                          (let uu____4076 = FStar_Syntax_Util.type_u () in
                           match uu____4076 with
                           | (t_phi,uu____4083) ->
                               let uu____4084 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____4084 with
                                | (phi2,uu____4092,f2) ->
                                    let e1 =
                                      let uu___104_4097 =
                                        FStar_Syntax_Util.refine (fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___104_4097.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___104_4097.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___104_4097.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____4116 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____4116 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____4125) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____4150 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____4150
            then
              let uu____4151 =
                FStar_Syntax_Print.term_to_string
                  (let uu___105_4152 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___105_4152.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___105_4152.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___105_4152.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____4151
            else ());
           (let uu____4171 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____4171 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____4179 ->
          let uu____4180 =
            let uu____4181 = FStar_Syntax_Print.term_to_string top in
            let uu____4182 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____4181
              uu____4182 in
          failwith uu____4180
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____4188 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____4189,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____4195,Some uu____4196) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____4204 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____4208 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____4209 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____4210 ->
          FStar_TypeChecker_Common.t_range
      | uu____4211 -> raise (FStar_Errors.Error ("Unsupported constant", r))
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
      | FStar_Syntax_Syntax.Total (t,uu____4222) ->
          let uu____4229 = FStar_Syntax_Util.type_u () in
          (match uu____4229 with
           | (k,u) ->
               let uu____4237 = tc_check_tot_or_gtot_term env t k in
               (match uu____4237 with
                | (t1,uu____4245,g) ->
                    let uu____4247 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____4247, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____4249) ->
          let uu____4256 = FStar_Syntax_Util.type_u () in
          (match uu____4256 with
           | (k,u) ->
               let uu____4264 = tc_check_tot_or_gtot_term env t k in
               (match uu____4264 with
                | (t1,uu____4272,g) ->
                    let uu____4274 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____4274, u, g)))
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
            let uu____4290 =
              let uu____4291 =
                let uu____4292 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____4292 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____4291 in
            uu____4290 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____4297 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____4297 with
           | (tc1,uu____4305,f) ->
               let uu____4307 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____4307 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4337 =
                        let uu____4338 = FStar_Syntax_Subst.compress head3 in
                        uu____4338.FStar_Syntax_Syntax.n in
                      match uu____4337 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4341,us) -> us
                      | uu____4347 -> [] in
                    let uu____4348 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____4348 with
                     | (uu____4361,args1) ->
                         let uu____4377 =
                           let uu____4389 = FStar_List.hd args1 in
                           let uu____4398 = FStar_List.tl args1 in
                           (uu____4389, uu____4398) in
                         (match uu____4377 with
                          | (res,args2) ->
                              let uu____4440 =
                                let uu____4445 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___86_4455  ->
                                          match uu___86_4455 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4461 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4461 with
                                               | (env1,uu____4468) ->
                                                   let uu____4471 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4471 with
                                                    | (e1,uu____4478,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____4445
                                  FStar_List.unzip in
                              (match uu____4440 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___106_4501 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___106_4501.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___106_4501.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4505 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4505 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____4508 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4508))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4516 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4517 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4521 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4521
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4524 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4524
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4528 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4528 FStar_Pervasives.snd
         | uu____4533 -> aux u)
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
            let uu____4554 =
              let uu____4555 =
                let uu____4558 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4558, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4555 in
            raise uu____4554 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4612 bs2 bs_expected1 =
              match uu____4612 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit
                            uu____4703)) ->
                             let uu____4706 =
                               let uu____4707 =
                                 let uu____4710 =
                                   let uu____4711 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4711 in
                                 let uu____4712 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4710, uu____4712) in
                               FStar_Errors.Error uu____4707 in
                             raise uu____4706
                         | (Some (FStar_Syntax_Syntax.Implicit
                            uu____4713),None ) ->
                             let uu____4716 =
                               let uu____4717 =
                                 let uu____4720 =
                                   let uu____4721 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4721 in
                                 let uu____4722 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4720, uu____4722) in
                               FStar_Errors.Error uu____4717 in
                             raise uu____4716
                         | uu____4723 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4727 =
                           let uu____4730 =
                             let uu____4731 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4731.FStar_Syntax_Syntax.n in
                           match uu____4730 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4736 ->
                               ((let uu____4738 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4738
                                 then
                                   let uu____4739 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4739
                                 else ());
                                (let uu____4741 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4741 with
                                 | (t,uu____4748,g1) ->
                                     let g2 =
                                       let uu____4751 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4752 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4751
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4752 in
                                     let g3 =
                                       let uu____4754 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4754 in
                                     (t, g3))) in
                         match uu____4727 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___107_4770 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___107_4770.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___107_4770.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4779 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4779 in
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
                  | uu____4881 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4885 = tc_binders env1 bs in
                  match uu____4885 with
                  | (bs1,envbody,g,uu____4906) ->
                      let uu____4907 =
                        let uu____4914 =
                          let uu____4915 = FStar_Syntax_Subst.compress body1 in
                          uu____4915.FStar_Syntax_Syntax.n in
                        match uu____4914 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4927) ->
                            let uu____4963 = tc_comp envbody c in
                            (match uu____4963 with
                             | (c1,uu____4974,g') ->
                                 let uu____4976 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4978 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), uu____4976, body1, uu____4978))
                        | uu____4981 -> (None, None, body1, g) in
                      (match uu____4907 with
                       | (copt,tacopt,body2,g1) ->
                           (None, bs1, [], copt, tacopt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____5040 =
                    let uu____5041 = FStar_Syntax_Subst.compress t2 in
                    uu____5041.FStar_Syntax_Syntax.n in
                  match uu____5040 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____5058 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____5070 -> failwith "Impossible");
                       (let uu____5074 = tc_binders env1 bs in
                        match uu____5074 with
                        | (bs1,envbody,g,uu____5096) ->
                            let uu____5097 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____5097 with
                             | (envbody1,uu____5116) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____5127;
                         FStar_Syntax_Syntax.tk = uu____5128;
                         FStar_Syntax_Syntax.pos = uu____5129;
                         FStar_Syntax_Syntax.vars = uu____5130;_},uu____5131)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____5157 -> failwith "Impossible");
                       (let uu____5161 = tc_binders env1 bs in
                        match uu____5161 with
                        | (bs1,envbody,g,uu____5183) ->
                            let uu____5184 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____5184 with
                             | (envbody1,uu____5203) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____5215) ->
                      let uu____5220 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____5220 with
                       | (uu____5249,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____5289 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____5289 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5352 c_expected2 =
                               match uu____5352 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____5413 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____5413)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____5430 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5430 in
                                        let uu____5431 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____5431)
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
                                               let uu____5472 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____5472 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5484 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____5484 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5511 =
                                                           let uu____5527 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____5527,
                                                             subst2) in
                                                         handle_more
                                                           uu____5511
                                                           c_expected4))
                                           | uu____5536 ->
                                               let uu____5537 =
                                                 let uu____5538 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____5538 in
                                               fail uu____5537 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____5554 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5554 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___108_5592 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___108_5592.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___108_5592.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___108_5592.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___108_5592.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___108_5592.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___108_5592.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___108_5592.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___108_5592.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___108_5592.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___108_5592.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___108_5592.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___108_5592.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___108_5592.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___108_5592.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___108_5592.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___108_5592.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___108_5592.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___108_5592.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___108_5592.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___108_5592.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___108_5592.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___108_5592.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___108_5592.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___108_5592.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___108_5592.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___108_5592.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5606  ->
                                     fun uu____5607  ->
                                       match (uu____5606, uu____5607) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5632 =
                                             let uu____5636 =
                                               let uu____5637 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5637
                                                 FStar_Pervasives.fst in
                                             tc_term uu____5636 t3 in
                                           (match uu____5632 with
                                            | (t4,uu____5649,uu____5650) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5657 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___109_5658
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___109_5658.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___109_5658.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5657 ::
                                                        letrec_binders
                                                  | uu____5659 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5662 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5662 with
                            | (envbody,bs1,g,c) ->
                                let uu____5694 =
                                  let uu____5698 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5698
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5694 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), None, envbody2, body1, g))))
                  | uu____5734 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5749 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5749
                      else
                        (let uu____5751 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5751 with
                         | (uu____5779,bs1,uu____5781,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, tacopt,
                               envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5806 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5806 with
          | (env1,topt) ->
              ((let uu____5818 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5818
                then
                  let uu____5819 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5819
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5823 = expected_function_typ1 env1 topt body in
                match uu____5823 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5858 =
                      tc_term
                        (let uu___110_5862 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___110_5862.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___110_5862.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___110_5862.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___110_5862.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___110_5862.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___110_5862.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___110_5862.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___110_5862.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___110_5862.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___110_5862.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___110_5862.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___110_5862.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___110_5862.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___110_5862.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___110_5862.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___110_5862.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___110_5862.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___110_5862.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___110_5862.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___110_5862.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___110_5862.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___110_5862.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___110_5862.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___110_5862.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___110_5862.FStar_TypeChecker_Env.is_native_tactic)
                         }) body1 in
                    (match uu____5858 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5871 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5871
                           then
                             let uu____5872 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5883 =
                               let uu____5884 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5884 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5872 uu____5883
                           else ());
                          (let uu____5886 =
                             let uu____5890 =
                               let uu____5893 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5893) in
                             check_expected_effect
                               (let uu___111_5898 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___111_5898.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___111_5898.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___111_5898.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___111_5898.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___111_5898.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___111_5898.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___111_5898.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___111_5898.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___111_5898.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___111_5898.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___111_5898.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___111_5898.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___111_5898.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___111_5898.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___111_5898.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___111_5898.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___111_5898.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___111_5898.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___111_5898.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___111_5898.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___111_5898.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___111_5898.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___111_5898.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___111_5898.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___111_5898.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___111_5898.FStar_TypeChecker_Env.is_native_tactic)
                                }) c_opt uu____5890 in
                           match uu____5886 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____5907 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5908 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5908) in
                                 if uu____5907
                                 then
                                   let uu____5909 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5909
                                 else
                                   (let guard2 =
                                      let uu____5912 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5912 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 let uu____5919 =
                                   let uu____5926 =
                                     let uu____5932 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     FStar_All.pipe_right uu____5932
                                       (fun _0_40  -> FStar_Util.Inl _0_40) in
                                   Some uu____5926 in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5919 in
                               let uu____5946 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5961 -> (e, t1, guard2)
                                      | uu____5969 ->
                                          let uu____5970 =
                                            if use_teq
                                            then
                                              let uu____5975 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5975)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5970 with
                                           | (e1,guard') ->
                                               let uu____5982 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5982)))
                                 | None  -> (e, tfun_computed, guard2) in
                               (match uu____5946 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____5995 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____5995 with
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
              (let uu____6032 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____6032
               then
                 let uu____6033 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____6034 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____6033
                   uu____6034
               else ());
              (let monadic_application uu____6072 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____6072 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___112_6109 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___112_6109.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___112_6109.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___112_6109.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____6110 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____6119 ->
                           let g =
                             let uu____6124 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____6124
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____6125 =
                             let uu____6126 =
                               let uu____6129 =
                                 let uu____6130 =
                                   let uu____6131 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____6131 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____6130 in
                               FStar_Syntax_Syntax.mk_Total uu____6129 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____6126 in
                           (uu____6125, g) in
                     (match uu____6110 with
                      | (cres2,guard1) ->
                          ((let uu____6142 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____6142
                            then
                              let uu____6143 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____6143
                            else ());
                           (let cres3 =
                              let uu____6146 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____6146
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
                                   fun uu____6169  ->
                                     match uu____6169 with
                                     | ((e,q),x,c) ->
                                         let uu____6192 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6192
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
                              let uu____6201 =
                                let uu____6202 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____6202.FStar_Syntax_Syntax.n in
                              match uu____6201 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____6206 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____6216  ->
                                         match uu____6216 with
                                         | (arg,uu____6224,uu____6225) -> arg
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
                                (let uu____6237 =
                                   let map_fun uu____6272 =
                                     match uu____6272 with
                                     | ((e,q),uu____6292,c) ->
                                         let uu____6298 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6298
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
                                            let uu____6328 =
                                              let uu____6331 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____6331, q) in
                                            ((Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____6328)) in
                                   let uu____6349 =
                                     let uu____6363 =
                                       let uu____6376 =
                                         let uu____6384 =
                                           let uu____6389 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____6389, None, chead1) in
                                         uu____6384 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____6376 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6363 in
                                   match uu____6349 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6484 =
                                         let uu____6485 =
                                           FStar_List.hd reverse_args in
                                         fst uu____6485 in
                                       let uu____6490 =
                                         let uu____6494 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6494 in
                                       (lifted_args, uu____6484, uu____6490) in
                                 match uu____6237 with
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
                                     let bind_lifted_args e uu___87_6562 =
                                       match uu___87_6562 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6604 =
                                               let uu____6607 =
                                                 let uu____6608 =
                                                   let uu____6616 =
                                                     let uu____6617 =
                                                       let uu____6618 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6618] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6617 e in
                                                   ((false, [lb]),
                                                     uu____6616) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6608 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6607 in
                                             uu____6604 None
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
                            let uu____6652 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6652 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6706 bs args1 =
                 match uu____6706 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6789))::rest,
                         (uu____6791,None )::uu____6792) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 = check_no_escape (Some head1) env fvs t in
                          let uu____6829 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6829 with
                           | (varg,uu____6840,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6853 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6853) in
                               let uu____6854 =
                                 let uu____6872 =
                                   let uu____6880 =
                                     let uu____6887 =
                                       let uu____6888 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____6888
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, None, uu____6887) in
                                   uu____6880 :: outargs in
                                 let uu____6898 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____6872, (arg :: arg_rets),
                                   uu____6898, fvs) in
                               tc_args head_info uu____6854 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit
                               uu____6958),Some (FStar_Syntax_Syntax.Implicit
                               uu____6959)) -> ()
                            | (None ,None ) -> ()
                            | (Some (FStar_Syntax_Syntax.Equality ),None ) ->
                                ()
                            | uu____6966 ->
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___113_6973 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___113_6973.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___113_6973.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6975 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6975
                             then
                               let uu____6976 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6976
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___114_6981 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___114_6981.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___114_6981.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___114_6981.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___114_6981.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___114_6981.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___114_6981.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___114_6981.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___114_6981.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___114_6981.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___114_6981.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___114_6981.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___114_6981.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___114_6981.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___114_6981.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___114_6981.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___114_6981.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___114_6981.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___114_6981.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___114_6981.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___114_6981.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___114_6981.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___114_6981.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___114_6981.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___114_6981.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___114_6981.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___114_6981.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             (let uu____6983 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6983
                              then
                                let uu____6984 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6985 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6986 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6984 uu____6985 uu____6986
                              else ());
                             (let uu____6988 = tc_term env2 e in
                              match uu____6988 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____7005 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____7005 in
                                  let uu____7006 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____7006
                                  then
                                    let subst2 =
                                      let uu____7011 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____7011 e1 in
                                    tc_args head_info
                                      (subst2, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        (x1 :: fvs)) rest rest'))))
                      | (uu____7059,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____7080) ->
                          let uu____7110 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____7110 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____7133 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____7133
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____7149 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____7149 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____7163 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____7163
                                            then
                                              let uu____7164 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____7164
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____7186 when Prims.op_Negation norm1 ->
                                     let uu____7187 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____7187
                                 | uu____7188 ->
                                     let uu____7189 =
                                       let uu____7190 =
                                         let uu____7193 =
                                           let uu____7194 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____7195 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____7194 uu____7195 in
                                         let uu____7202 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____7193, uu____7202) in
                                       FStar_Errors.Error uu____7190 in
                                     raise uu____7189 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____7215 =
                   let uu____7216 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____7216.FStar_Syntax_Syntax.n in
                 match uu____7215 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____7224 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7288 = tc_term env1 e in
                           (match uu____7288 with
                            | (e1,c,g_e) ->
                                let uu____7301 = tc_args1 env1 tl1 in
                                (match uu____7301 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7323 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7323))) in
                     let uu____7334 = tc_args1 env args in
                     (match uu____7334 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7356 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7376  ->
                                      match uu____7376 with
                                      | (uu____7384,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7356 in
                          let ml_or_tot t r1 =
                            let uu____7400 = FStar_Options.ml_ish () in
                            if uu____7400
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7403 =
                              let uu____7406 =
                                let uu____7407 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7407
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7406 in
                            ml_or_tot uu____7403 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7416 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7416
                            then
                              let uu____7417 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7418 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7419 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7417 uu____7418 uu____7419
                            else ());
                           (let uu____7422 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7422);
                           (let comp =
                              let uu____7424 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7429  ->
                                   fun out  ->
                                     match uu____7429 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7424 in
                            let uu____7438 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7445 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7438, comp, uu____7445))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7448;
                        FStar_Syntax_Syntax.tk = uu____7449;
                        FStar_Syntax_Syntax.pos = uu____7450;
                        FStar_Syntax_Syntax.vars = uu____7451;_},uu____7452)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7530 = tc_term env1 e in
                           (match uu____7530 with
                            | (e1,c,g_e) ->
                                let uu____7543 = tc_args1 env1 tl1 in
                                (match uu____7543 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7565 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7565))) in
                     let uu____7576 = tc_args1 env args in
                     (match uu____7576 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7598 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7618  ->
                                      match uu____7618 with
                                      | (uu____7626,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7598 in
                          let ml_or_tot t r1 =
                            let uu____7642 = FStar_Options.ml_ish () in
                            if uu____7642
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7645 =
                              let uu____7648 =
                                let uu____7649 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7649
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7648 in
                            ml_or_tot uu____7645 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7658 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7658
                            then
                              let uu____7659 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7660 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7661 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7659 uu____7660 uu____7661
                            else ());
                           (let uu____7664 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7664);
                           (let comp =
                              let uu____7666 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7671  ->
                                   fun out  ->
                                     match uu____7671 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7666 in
                            let uu____7680 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7687 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7680, comp, uu____7687))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7702 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7702 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7738) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7744,uu____7745)
                     -> check_function_app t
                 | uu____7774 ->
                     let uu____7775 =
                       let uu____7776 =
                         let uu____7779 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7779, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7776 in
                     raise uu____7775 in
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
                  let uu____7834 =
                    FStar_List.fold_left2
                      (fun uu____7847  ->
                         fun uu____7848  ->
                           fun uu____7849  ->
                             match (uu____7847, uu____7848, uu____7849) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7893 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7893 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7905 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7905 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7907 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7907) &&
                                              (let uu____7908 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7908)) in
                                       let uu____7909 =
                                         let uu____7915 =
                                           let uu____7921 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7921] in
                                         FStar_List.append seen uu____7915 in
                                       let uu____7926 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7909, uu____7926, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7834 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____7955 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7955
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7957 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7957 with | (c2,g) -> (e, c2, g)))
              | uu____7969 ->
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
        let uu____7991 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7991 with
        | (pattern,when_clause,branch_exp) ->
            let uu____8017 = branch1 in
            (match uu____8017 with
             | (cpat,uu____8037,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____8075 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____8075 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____8092 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____8092
                         then
                           let uu____8093 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____8094 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____8093 uu____8094
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____8097 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____8097 with
                         | (env1,uu____8108) ->
                             let env11 =
                               let uu___115_8112 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___115_8112.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___115_8112.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___115_8112.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___115_8112.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___115_8112.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___115_8112.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___115_8112.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___115_8112.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___115_8112.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___115_8112.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___115_8112.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___115_8112.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___115_8112.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___115_8112.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___115_8112.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___115_8112.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___115_8112.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___115_8112.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___115_8112.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___115_8112.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___115_8112.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___115_8112.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___115_8112.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___115_8112.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___115_8112.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___115_8112.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____8115 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____8115
                               then
                                 let uu____8116 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____8117 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____8116 uu____8117
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____8120 = tc_tot_or_gtot_term env12 exp in
                               match uu____8120 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___116_8134 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___116_8134.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___116_8134.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___116_8134.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____8135 =
                                     let g' =
                                       FStar_TypeChecker_Rel.teq env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     let g2 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g' in
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let uu____8139 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2 in
                                     FStar_All.pipe_right uu____8139
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____8150 =
                                       let uu____8151 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____8151 in
                                     if uu____8150
                                     then
                                       let unresolved =
                                         let uu____8158 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____8158
                                           FStar_Util.set_elements in
                                       let uu____8172 =
                                         let uu____8173 =
                                           let uu____8176 =
                                             let uu____8177 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____8178 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____8179 =
                                               let uu____8180 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____8188  ->
                                                         match uu____8188
                                                         with
                                                         | (u,uu____8192) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____8180
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____8177 uu____8178
                                               uu____8179 in
                                           (uu____8176,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____8173 in
                                       raise uu____8172
                                     else ());
                                    (let uu____8196 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____8196
                                     then
                                       let uu____8197 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____8197
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____8205 =
                   let uu____8209 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____8209
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____8205 with
                  | (scrutinee_env,uu____8222) ->
                      let uu____8225 = tc_pat true pat_t pattern in
                      (match uu____8225 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____8247 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____8262 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____8262
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____8270 =
                                      let uu____8274 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____8274 e in
                                    match uu____8270 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____8247 with
                            | (when_clause1,g_when) ->
                                let uu____8294 = tc_term pat_env branch_exp in
                                (match uu____8294 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____8313 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_41  -> Some _0_41)
                                             uu____8313 in
                                     let uu____8315 =
                                       let eqs =
                                         let uu____8321 =
                                           let uu____8322 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____8322 in
                                         if uu____8321
                                         then None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____8327 -> None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8336 -> None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8337 -> None
                                            | uu____8338 ->
                                                let uu____8339 =
                                                  let uu____8340 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8340 pat_t
                                                    scrutinee_tm e in
                                                Some uu____8339) in
                                       let uu____8341 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____8341 with
                                       | (c1,g_branch1) ->
                                           let uu____8351 =
                                             match (eqs, when_condition) with
                                             | uu____8358 when
                                                 let uu____8363 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8363
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____8371 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8372 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8371, uu____8372)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____8379 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8379 in
                                                 let uu____8380 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8381 =
                                                   let uu____8382 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8382 g_when in
                                                 (uu____8380, uu____8381)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____8388 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8388, g_when) in
                                           (match uu____8351 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____8396 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____8397 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8396, uu____8397,
                                                  g_branch1)) in
                                     (match uu____8315 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8410 =
                                              let uu____8411 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8411 in
                                            if uu____8410
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8442 =
                                                     let uu____8443 =
                                                       let uu____8444 =
                                                         let uu____8446 =
                                                           let uu____8450 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8450 in
                                                         snd uu____8446 in
                                                       FStar_List.length
                                                         uu____8444 in
                                                     uu____8443 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8442
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____8460 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8460 with
                                                     | None  -> []
                                                     | uu____8471 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None in
                                                         let disc1 =
                                                           let uu____8481 =
                                                             let uu____8482 =
                                                               let uu____8483
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8483] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8482 in
                                                           uu____8481 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8488 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool in
                                                         [uu____8488]
                                                   else [] in
                                                 let fail uu____8496 =
                                                   let uu____8497 =
                                                     let uu____8498 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____8499 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____8500 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8498 uu____8499
                                                       uu____8500 in
                                                   failwith uu____8497 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8521) ->
                                                       head_constructor t1
                                                   | uu____8527 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____8530 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____8530
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____8532 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____8541;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8542;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8543;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8544;_},uu____8545)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8568 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____8570 =
                                                       let uu____8571 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8571
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____8570]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8572 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8582 =
                                                       let uu____8583 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8583 in
                                                     if uu____8582
                                                     then []
                                                     else
                                                       (let uu____8590 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8590)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8596 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8602 =
                                                       let uu____8603 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8603 in
                                                     if uu____8602
                                                     then []
                                                     else
                                                       (let uu____8610 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8610)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8637 =
                                                       let uu____8638 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8638 in
                                                     if uu____8637
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8647 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8663
                                                                     ->
                                                                    match uu____8663
                                                                    with
                                                                    | 
                                                                    (ei,uu____8670)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8680
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8680
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8691
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8700
                                                                    =
                                                                    let uu____8701
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None in
                                                                    let uu____8706
                                                                    =
                                                                    let uu____8707
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8707] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8701
                                                                    uu____8706 in
                                                                    uu____8700
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8647
                                                            FStar_List.flatten in
                                                        let uu____8719 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8719
                                                          sub_term_guards)
                                                 | uu____8723 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8735 =
                                                   let uu____8736 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8736 in
                                                 if uu____8735
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8739 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8739 in
                                                    let uu____8742 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8742 with
                                                    | (k,uu____8746) ->
                                                        let uu____8747 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8747
                                                         with
                                                         | (t1,uu____8752,uu____8753)
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
                                          ((let uu____8759 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8759
                                            then
                                              let uu____8760 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8760
                                            else ());
                                           (let uu____8762 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8762, branch_guard, c1,
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
          let uu____8780 = check_let_bound_def true env1 lb in
          (match uu____8780 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8794 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____8803 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____8803, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8806 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8806
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8808 =
                      let uu____8813 =
                        let uu____8819 =
                          let uu____8824 =
                            let uu____8832 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8832) in
                          [uu____8824] in
                        FStar_TypeChecker_Util.generalize env1 uu____8819 in
                      FStar_List.hd uu____8813 in
                    match uu____8808 with
                    | (uu____8861,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8794 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8872 =
                      let uu____8877 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8877
                      then
                        let uu____8882 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8882 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8899 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____8899
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8900 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos in
                                 (uu____8900, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8918 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8918
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8926 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8926
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____8872 with
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
                           let uu____8958 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8958,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8977 -> failwith "Impossible"
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
            let uu___117_8998 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___117_8998.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___117_8998.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___117_8998.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___117_8998.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___117_8998.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___117_8998.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___117_8998.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___117_8998.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___117_8998.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___117_8998.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___117_8998.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___117_8998.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___117_8998.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___117_8998.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___117_8998.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___117_8998.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___117_8998.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___117_8998.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___117_8998.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___117_8998.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___117_8998.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___117_8998.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___117_8998.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___117_8998.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___117_8998.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___117_8998.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____8999 =
            let uu____9005 =
              let uu____9006 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____9006 FStar_Pervasives.fst in
            check_let_bound_def false uu____9005 lb in
          (match uu____8999 with
           | (e1,uu____9018,c1,g1,annotated) ->
               let x =
                 let uu___118_9023 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___118_9023.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___118_9023.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____9024 =
                 let uu____9027 =
                   let uu____9028 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____9028] in
                 FStar_Syntax_Subst.open_term uu____9027 e2 in
               (match uu____9024 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = fst xbinder in
                    let uu____9040 =
                      let uu____9044 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____9044 e21 in
                    (match uu____9040 with
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
                           let uu____9059 =
                             let uu____9062 =
                               let uu____9063 =
                                 let uu____9071 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____9071) in
                               FStar_Syntax_Syntax.Tm_let uu____9063 in
                             FStar_Syntax_Syntax.mk uu____9062 in
                           uu____9059
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____9086 =
                             let uu____9087 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____9088 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____9087
                               c1.FStar_Syntax_Syntax.res_typ uu____9088 e11 in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.NonTrivial _0_42)
                             uu____9086 in
                         let g21 =
                           let uu____9090 =
                             let uu____9091 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____9091 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____9090 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____9093 =
                           let uu____9094 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____9094 in
                         if uu____9093
                         then
                           let tt =
                             let uu____9100 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____9100 FStar_Option.get in
                           ((let uu____9104 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____9104
                             then
                               let uu____9105 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____9106 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____9105 uu____9106
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____9111 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____9111
                             then
                               let uu____9112 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____9113 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____9112 uu____9113
                             else ());
                            (e4,
                              ((let uu___119_9115 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___119_9115.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___119_9115.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___119_9115.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____9116 -> failwith "Impossible"
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
          let uu____9137 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9137 with
           | (lbs1,e21) ->
               let uu____9148 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9148 with
                | (env0,topt) ->
                    let uu____9159 = build_let_rec_env true env0 lbs1 in
                    (match uu____9159 with
                     | (lbs2,rec_env) ->
                         let uu____9170 = check_let_recs rec_env lbs2 in
                         (match uu____9170 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____9182 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____9182
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____9186 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____9186
                                  (fun _0_43  -> Some _0_43) in
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
                                     let uu____9211 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____9233 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____9233))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____9211 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____9253  ->
                                           match uu____9253 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____9278 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____9278 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____9287 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____9287 with
                                | (lbs5,e22) ->
                                    ((let uu____9299 =
                                        FStar_TypeChecker_Rel.discharge_guard
                                          env1 g_lbs1 in
                                      FStar_All.pipe_right uu____9299
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1));
                                     (let uu____9300 =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_let
                                              ((true, lbs5), e22)))
                                          (Some
                                             (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos in
                                      (uu____9300, cres,
                                        FStar_TypeChecker_Rel.trivial_guard)))))))))
      | uu____9317 -> failwith "Impossible"
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
          let uu____9338 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9338 with
           | (lbs1,e21) ->
               let uu____9349 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9349 with
                | (env0,topt) ->
                    let uu____9360 = build_let_rec_env false env0 lbs1 in
                    (match uu____9360 with
                     | (lbs2,rec_env) ->
                         let uu____9371 = check_let_recs rec_env lbs2 in
                         (match uu____9371 with
                          | (lbs3,g_lbs) ->
                              let uu____9382 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___120_9393 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___120_9393.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___120_9393.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___121_9395 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___121_9395.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___121_9395.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___121_9395.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___121_9395.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____9382 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____9412 = tc_term env2 e21 in
                                   (match uu____9412 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9423 =
                                            let uu____9424 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9424 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9423 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___122_9428 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___122_9428.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___122_9428.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___122_9428.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9429 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9429 with
                                         | (lbs5,e23) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | Some uu____9458 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres in
                                                  let cres3 =
                                                    let uu___123_9463 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___123_9463.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___123_9463.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___123_9463.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9466 -> failwith "Impossible"
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
          let uu____9489 =
            let uu____9492 =
              let uu____9493 = FStar_Syntax_Subst.compress t in
              uu____9493.FStar_Syntax_Syntax.n in
            let uu____9496 =
              let uu____9497 = FStar_Syntax_Subst.compress lbdef in
              uu____9497.FStar_Syntax_Syntax.n in
            (uu____9492, uu____9496) in
          match uu____9489 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9503,uu____9504)) ->
              let actuals1 =
                let uu____9538 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9538
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____9563 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9563) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____9581 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____9581) in
                  let msg =
                    let uu____9589 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____9590 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9589 uu____9590 formals_msg actuals_msg in
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____9595 ->
              let uu____9598 =
                let uu____9599 =
                  let uu____9602 =
                    let uu____9603 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____9604 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9603 uu____9604 in
                  (uu____9602, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____9599 in
              raise uu____9598 in
        let uu____9605 =
          FStar_List.fold_left
            (fun uu____9612  ->
               fun lb  ->
                 match uu____9612 with
                 | (lbs1,env1) ->
                     let uu____9624 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9624 with
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
                              (let uu____9638 =
                                 let uu____9642 =
                                   let uu____9643 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left FStar_Pervasives.fst
                                     uu____9643 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___124_9648 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___124_9648.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___124_9648.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___124_9648.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___124_9648.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___124_9648.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___124_9648.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___124_9648.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___124_9648.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___124_9648.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___124_9648.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___124_9648.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___124_9648.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___124_9648.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___124_9648.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___124_9648.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___124_9648.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___124_9648.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___124_9648.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___124_9648.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___124_9648.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___124_9648.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___124_9648.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___124_9648.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___124_9648.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___124_9648.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___124_9648.FStar_TypeChecker_Env.is_native_tactic)
                                    }) t uu____9642 in
                               match uu____9638 with
                               | (t1,uu____9650,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9654 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9654);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9656 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9656
                            then
                              let uu___125_9657 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___125_9657.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___125_9657.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___125_9657.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___125_9657.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___125_9657.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___125_9657.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___125_9657.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___125_9657.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___125_9657.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___125_9657.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___125_9657.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___125_9657.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___125_9657.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___125_9657.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___125_9657.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___125_9657.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___125_9657.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___125_9657.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___125_9657.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___125_9657.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___125_9657.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___125_9657.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___125_9657.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___125_9657.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___125_9657.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___125_9657.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___126_9667 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___126_9667.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___126_9667.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9605 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9681 =
        let uu____9686 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9698 =
                     let uu____9699 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____9699.FStar_Syntax_Syntax.n in
                   match uu____9698 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9702 -> ()
                   | uu____9717 ->
                       let uu____9718 =
                         let uu____9719 =
                           let uu____9722 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____9722) in
                         FStar_Errors.Error uu____9719 in
                       raise uu____9718);
                  (let uu____9723 =
                     let uu____9727 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____9727
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____9723 with
                   | (e,c,g) ->
                       ((let uu____9734 =
                           let uu____9735 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____9735 in
                         if uu____9734
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
        FStar_All.pipe_right uu____9686 FStar_List.unzip in
      match uu____9681 with
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
        let uu____9764 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9764 with
        | (env1,uu____9774) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9780 = check_lbtyp top_level env lb in
            (match uu____9780 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9806 =
                     tc_maybe_toplevel_term
                       (let uu___127_9810 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___127_9810.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___127_9810.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___127_9810.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___127_9810.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___127_9810.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___127_9810.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___127_9810.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___127_9810.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___127_9810.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___127_9810.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___127_9810.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___127_9810.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___127_9810.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___127_9810.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___127_9810.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___127_9810.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___127_9810.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___127_9810.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___127_9810.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___127_9810.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___127_9810.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___127_9810.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___127_9810.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___127_9810.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___127_9810.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___127_9810.FStar_TypeChecker_Env.is_native_tactic)
                        }) e11 in
                   match uu____9806 with
                   | (e12,c1,g1) ->
                       let uu____9819 =
                         let uu____9822 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9825  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9822 e12 c1 wf_annot in
                       (match uu____9819 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9835 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9835
                              then
                                let uu____9836 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9837 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9838 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9836 uu____9837 uu____9838
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
        | uu____9864 ->
            let uu____9865 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9865 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9892 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9892)
                 else
                   (let uu____9897 = FStar_Syntax_Util.type_u () in
                    match uu____9897 with
                    | (k,uu____9908) ->
                        let uu____9909 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9909 with
                         | (t2,uu____9921,g) ->
                             ((let uu____9924 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9924
                               then
                                 let uu____9925 =
                                   let uu____9926 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9926 in
                                 let uu____9927 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9925 uu____9927
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9930 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9930))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9935  ->
      match uu____9935 with
      | (x,imp) ->
          let uu____9946 = FStar_Syntax_Util.type_u () in
          (match uu____9946 with
           | (tu,u) ->
               ((let uu____9958 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9958
                 then
                   let uu____9959 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9960 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9961 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9959 uu____9960 uu____9961
                 else ());
                (let uu____9963 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9963 with
                 | (t,uu____9974,g) ->
                     let x1 =
                       ((let uu___128_9979 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___128_9979.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___128_9979.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9981 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9981
                       then
                         let uu____9982 =
                           FStar_Syntax_Print.bv_to_string (fst x1) in
                         let uu____9983 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9982 uu____9983
                       else ());
                      (let uu____9985 = push_binding env x1 in
                       (x1, uu____9985, g, u))))))
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
            let uu____10036 = tc_binder env1 b in
            (match uu____10036 with
             | (b1,env',g,u) ->
                 let uu____10059 = aux env' bs2 in
                 (match uu____10059 with
                  | (bs3,env'1,g',us) ->
                      let uu____10088 =
                        let uu____10089 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____10089 in
                      ((b1 :: bs3), env'1, uu____10088, (u :: us)))) in
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
          (fun uu____10132  ->
             fun uu____10133  ->
               match (uu____10132, uu____10133) with
               | ((t,imp),(args1,g)) ->
                   let uu____10170 = tc_term env1 t in
                   (match uu____10170 with
                    | (t1,uu____10180,g') ->
                        let uu____10182 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____10182))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____10200  ->
             match uu____10200 with
             | (pats1,g) ->
                 let uu____10214 = tc_args env p in
                 (match uu____10214 with
                  | (args,g') ->
                      let uu____10222 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____10222))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____10230 = tc_maybe_toplevel_term env e in
      match uu____10230 with
      | (e1,c,g) ->
          let uu____10240 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____10240
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____10250 =
               let uu____10253 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____10253
               then
                 let uu____10256 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____10256, false)
               else
                 (let uu____10258 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____10258, true)) in
             match uu____10250 with
             | (target_comp,allow_ghost) ->
                 let uu____10264 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____10264 with
                  | Some g' ->
                      let uu____10270 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____10270)
                  | uu____10271 ->
                      if allow_ghost
                      then
                        let uu____10276 =
                          let uu____10277 =
                            let uu____10280 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____10280, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____10277 in
                        raise uu____10276
                      else
                        (let uu____10285 =
                           let uu____10286 =
                             let uu____10289 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____10289, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____10286 in
                         raise uu____10285)))
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
      let uu____10302 = tc_tot_or_gtot_term env t in
      match uu____10302 with
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
      (let uu____10324 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10324
       then
         let uu____10325 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____10325
       else ());
      (let env1 =
         let uu___129_10328 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___129_10328.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___129_10328.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___129_10328.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___129_10328.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___129_10328.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___129_10328.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___129_10328.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___129_10328.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___129_10328.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___129_10328.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___129_10328.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___129_10328.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___129_10328.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___129_10328.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___129_10328.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___129_10328.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___129_10328.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___129_10328.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___129_10328.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___129_10328.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___129_10328.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___129_10328.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___129_10328.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___129_10328.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___129_10328.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____10331 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10347) ->
             let uu____10348 =
               let uu____10349 =
                 let uu____10352 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____10352) in
               FStar_Errors.Error uu____10349 in
             raise uu____10348 in
       match uu____10331 with
       | (t,c,g) ->
           let uu____10362 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____10362
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10369 =
                let uu____10370 =
                  let uu____10373 =
                    let uu____10374 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10374 in
                  let uu____10375 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____10373, uu____10375) in
                FStar_Errors.Error uu____10370 in
              raise uu____10369))
let level_of_type_fail env e t =
  let uu____10400 =
    let uu____10401 =
      let uu____10404 =
        let uu____10405 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10405 t in
      let uu____10406 = FStar_TypeChecker_Env.get_range env in
      (uu____10404, uu____10406) in
    FStar_Errors.Error uu____10401 in
  raise uu____10400
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____10426 =
            let uu____10427 = FStar_Syntax_Util.unrefine t1 in
            uu____10427.FStar_Syntax_Syntax.n in
          match uu____10426 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10431 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____10434 = FStar_Syntax_Util.type_u () in
                 match uu____10434 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___132_10440 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___132_10440.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___132_10440.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___132_10440.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___132_10440.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___132_10440.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___132_10440.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___132_10440.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___132_10440.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___132_10440.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___132_10440.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___132_10440.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___132_10440.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___132_10440.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___132_10440.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___132_10440.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___132_10440.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___132_10440.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___132_10440.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___132_10440.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___132_10440.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___132_10440.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___132_10440.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___132_10440.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___132_10440.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___132_10440.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___132_10440.FStar_TypeChecker_Env.is_native_tactic)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____10444 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____10444
                       | uu____10445 ->
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
      let uu____10456 =
        let uu____10457 = FStar_Syntax_Subst.compress e in
        uu____10457.FStar_Syntax_Syntax.n in
      match uu____10456 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10462 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10467 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10490 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10501) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10526,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10541) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10548 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10548 with | ((uu____10559,t),uu____10561) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10564,(FStar_Util.Inl t,uu____10566),uu____10567) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10603,(FStar_Util.Inr c,uu____10605),uu____10606) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)) None
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10649;
             FStar_Syntax_Syntax.pos = uu____10650;
             FStar_Syntax_Syntax.vars = uu____10651;_},us)
          ->
          let uu____10657 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10657 with
           | ((us',t),uu____10670) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10682 =
                     let uu____10683 =
                       let uu____10686 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10686) in
                     FStar_Errors.Error uu____10683 in
                   raise uu____10682)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10693 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10694 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10702) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10719 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10719 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10730  ->
                      match uu____10730 with
                      | (b,uu____10734) ->
                          let uu____10735 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10735) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10740 = universe_of_aux env res in
                 level_of_type env res uu____10740 in
               let u_c =
                 let uu____10742 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10742 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10745 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10745 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____10815 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10825 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10855 ->
                let uu____10856 = universe_of_aux env hd3 in
                (uu____10856, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10866 ->
                let uu____10867 = universe_of_aux env hd3 in
                (uu____10867, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10877 ->
                let uu____10886 = universe_of_aux env hd3 in
                (uu____10886, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10896 ->
                let uu____10901 = universe_of_aux env hd3 in
                (uu____10901, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10911 ->
                let uu____10929 = universe_of_aux env hd3 in
                (uu____10929, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10939 ->
                let uu____10944 = universe_of_aux env hd3 in
                (uu____10944, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10954 ->
                let uu____10955 = universe_of_aux env hd3 in
                (uu____10955, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10965 ->
                let uu____10973 = universe_of_aux env hd3 in
                (uu____10973, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____10983 ->
                let uu____10988 = universe_of_aux env hd3 in
                (uu____10988, args1)
            | FStar_Syntax_Syntax.Tm_type uu____10998 ->
                let uu____10999 = universe_of_aux env hd3 in
                (uu____10999, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____11009,hd4::uu____11011) ->
                let uu____11058 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____11058 with
                 | (uu____11068,uu____11069,hd5) ->
                     let uu____11085 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____11085 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____11120 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____11122 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____11122 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____11157 ->
                let uu____11158 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____11158 with
                 | (env1,uu____11172) ->
                     let env2 =
                       let uu___133_11176 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___133_11176.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___133_11176.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___133_11176.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___133_11176.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___133_11176.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___133_11176.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___133_11176.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___133_11176.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___133_11176.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___133_11176.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___133_11176.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___133_11176.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___133_11176.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___133_11176.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___133_11176.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___133_11176.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___133_11176.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___133_11176.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___133_11176.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___133_11176.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___133_11176.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___133_11176.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___133_11176.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___133_11176.FStar_TypeChecker_Env.is_native_tactic)
                       } in
                     ((let uu____11178 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____11178
                       then
                         let uu____11179 =
                           let uu____11180 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____11180 in
                         let uu____11181 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____11179 uu____11181
                       else ());
                      (let uu____11183 = tc_term env2 hd3 in
                       match uu____11183 with
                       | (uu____11196,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____11197;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____11199;
                                        FStar_Syntax_Syntax.comp =
                                          uu____11200;_},g)
                           ->
                           ((let uu____11210 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____11210
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____11218 = type_of_head true hd1 args in
          (match uu____11218 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____11247 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____11247 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____11284 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____11284)))
      | FStar_Syntax_Syntax.Tm_match (uu____11287,hd1::uu____11289) ->
          let uu____11336 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____11336 with
           | (uu____11339,uu____11340,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11356,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____11392 = universe_of_aux env e in
      level_of_type env e uu____11392
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____11407 = tc_binders env tps in
      match uu____11407 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))