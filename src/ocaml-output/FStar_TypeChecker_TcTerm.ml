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
           let uu____38 =
             let uu____39 =
               let uu____40 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____41 =
                 let uu____43 = FStar_Syntax_Syntax.as_arg tl1 in [uu____43] in
               uu____40 :: uu____41 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____39 in
           uu____38 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)
      vs FStar_Syntax_Util.lex_top
let is_eq: FStar_Syntax_Syntax.arg_qualifier option -> Prims.bool =
  fun uu___82_51  ->
    match uu___82_51 with
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
            | uu____98 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____104 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____104 with
                 | None  -> t1
                 | Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____113 =
                          let msg =
                            match head_opt with
                            | None  ->
                                let uu____115 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____115
                            | Some head1 ->
                                let uu____117 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____118 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____117 uu____118 in
                          let uu____119 =
                            let uu____120 =
                              let uu____123 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____123) in
                            FStar_Errors.Error uu____120 in
                          raise uu____119 in
                        let s =
                          let uu____125 =
                            let uu____126 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives.fst
                              uu____126 in
                          FStar_TypeChecker_Util.new_uvar env uu____125 in
                        let uu____131 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____131 with
                        | Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____135 -> fail ())) in
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
        let uu____166 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____166 then s else (FStar_Syntax_Syntax.NT ((fst b), v1)) :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___89_180 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___89_180.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___89_180.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____183  ->
             let uu____184 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____184 t)
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
            let uu____223 =
              let uu____224 = FStar_Syntax_Subst.compress t in
              uu____224.FStar_Syntax_Syntax.n in
            match uu____223 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____227,c) ->
                let uu____239 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____239
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____241 =
                    let uu____242 = FStar_Syntax_Subst.compress t1 in
                    uu____242.FStar_Syntax_Syntax.n in
                  (match uu____241 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____246 -> false
                   | uu____247 -> true)
                else false
            | uu____249 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____252 =
                  let uu____255 =
                    (let uu____258 = should_return t in
                     Prims.op_Negation uu____258) ||
                      (let uu____260 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____260) in
                  if uu____255
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____252
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____268 =
            let uu____272 = FStar_TypeChecker_Env.expected_typ env in
            match uu____272 with
            | None  -> let uu____277 = memo_tk e t in (uu____277, lc, guard)
            | Some t' ->
                ((let uu____280 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____280
                  then
                    let uu____281 = FStar_Syntax_Print.term_to_string t in
                    let uu____282 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____281
                      uu____282
                  else ());
                 (let uu____284 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____284 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____295 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____295 with
                       | (e2,g) ->
                           ((let uu____304 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____304
                             then
                               let uu____305 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____306 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____307 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____308 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____305 uu____306 uu____307 uu____308
                             else ());
                            (let msg =
                               let uu____314 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____314
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_29  -> Some _0_29)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____329 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____329 with
                             | (lc2,g2) ->
                                 let uu____337 = memo_tk e2 t' in
                                 (uu____337, (set_lcomp_result lc2 t'), g2)))))) in
          match uu____268 with
          | (e1,lc1,g) ->
              ((let uu____345 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____345
                then
                  let uu____346 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____346
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
        let uu____363 = FStar_TypeChecker_Env.expected_typ env in
        match uu____363 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____369 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____369 with
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
      fun uu____391  ->
        match uu____391 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____411 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____411
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____413 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____413
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____415 =
              match copt with
              | Some uu____422 -> (copt, c)
              | None  ->
                  let uu____424 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Syntax_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____426 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____426)) in
                  if uu____424
                  then
                    let uu____430 =
                      let uu____432 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      Some uu____432 in
                    (uu____430, c)
                  else
                    (let uu____435 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____435
                     then let uu____439 = tot_or_gtot c in (None, uu____439)
                     else
                       (let uu____442 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____442
                        then
                          let uu____446 =
                            let uu____448 = tot_or_gtot c in Some uu____448 in
                          (uu____446, c)
                        else (None, c))) in
            (match uu____415 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | None  -> (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | Some expected_c ->
                      let uu____464 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____464 with
                       | (e1,uu____472,g) ->
                           let g1 =
                             let uu____475 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____475
                               "could not prove post-condition" g in
                           ((let uu____477 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____477
                             then
                               let uu____478 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____479 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____478 uu____479
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard env uu____501 =
  match uu____501 with
  | (te,kt,f) ->
      let uu____508 = FStar_TypeChecker_Rel.guard_form f in
      (match uu____508 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____513 =
             let uu____514 =
               let uu____517 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____518 = FStar_TypeChecker_Env.get_range env in
               (uu____517, uu____518) in
             FStar_Errors.Error uu____514 in
           raise uu____513)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____525 = FStar_TypeChecker_Env.expected_typ env in
    match uu____525 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____528 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____528
let check_smt_pat env t bs c =
  let uu____563 = FStar_Syntax_Util.is_smt_lemma t in
  if uu____563
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____564;
          FStar_Syntax_Syntax.effect_name = uu____565;
          FStar_Syntax_Syntax.result_typ = uu____566;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____570)::[];
          FStar_Syntax_Syntax.flags = uu____571;_}
        ->
        let pat_vars =
          let uu____605 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats in
          FStar_Syntax_Free.names uu____605 in
        let uu____606 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____622  ->
                  match uu____622 with
                  | (b,uu____626) ->
                      let uu____627 = FStar_Util.set_mem b pat_vars in
                      Prims.op_Negation uu____627)) in
        (match uu____606 with
         | None  -> ()
         | Some (x,uu____631) ->
             let uu____634 =
               let uu____635 = FStar_Syntax_Print.bv_to_string x in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____635 in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____634)
    | uu____636 -> failwith "Impossible"
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
        let uu____657 =
          let uu____658 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____658 in
        if uu____657
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___90_676 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___90_676.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___90_676.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___90_676.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___90_676.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___90_676.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___90_676.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___90_676.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___90_676.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___90_676.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___90_676.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___90_676.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___90_676.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___90_676.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___90_676.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___90_676.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___90_676.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___90_676.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___90_676.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___90_676.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___90_676.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___90_676.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___90_676.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___90_676.FStar_TypeChecker_Env.qname_and_index)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____704  ->
                           match uu____704 with
                           | (b,uu____709) ->
                               let t =
                                 let uu____711 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____711 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____713 -> []
                                | FStar_Syntax_Syntax.Tm_arrow uu____714 ->
                                    []
                                | uu____722 ->
                                    let uu____723 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____723]))) in
                 let as_lex_list dec =
                   let uu____728 = FStar_Syntax_Util.head_and_args dec in
                   match uu____728 with
                   | (head1,uu____739) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____755 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____758 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___83_764  ->
                           match uu___83_764 with
                           | FStar_Syntax_Syntax.DECREASES uu____765 -> true
                           | uu____768 -> false)) in
                 match uu____758 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____772 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____778 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____790 =
                 match uu____790 with
                 | (l,t) ->
                     let uu____799 =
                       let uu____800 = FStar_Syntax_Subst.compress t in
                       uu____800.FStar_Syntax_Syntax.n in
                     (match uu____799 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____838  ->
                                    match uu____838 with
                                    | (x,imp) ->
                                        let uu____845 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____845
                                        then
                                          let uu____848 =
                                            let uu____849 =
                                              let uu____851 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              Some uu____851 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____849
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____848, imp)
                                        else (x, imp))) in
                          let uu____853 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____853 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____866 =
                                   let uu____867 =
                                     let uu____868 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____869 =
                                       let uu____871 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____871] in
                                     uu____868 :: uu____869 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____867 in
                                 uu____866 None r in
                               let uu____876 = FStar_Util.prefix formals2 in
                               (match uu____876 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___91_902 = last1 in
                                      let uu____903 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___91_902.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___91_902.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____903
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____920 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____920
                                      then
                                        let uu____921 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____922 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____923 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____921 uu____922 uu____923
                                      else ());
                                     (l, t'))))
                      | uu____927 ->
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
        (let uu___92_1200 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___92_1200.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___92_1200.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___92_1200.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___92_1200.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___92_1200.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___92_1200.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___92_1200.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___92_1200.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___92_1200.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___92_1200.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___92_1200.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___92_1200.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___92_1200.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___92_1200.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___92_1200.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___92_1200.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___92_1200.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___92_1200.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___92_1200.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___92_1200.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___92_1200.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___92_1200.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___92_1200.FStar_TypeChecker_Env.qname_and_index)
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
      (let uu____1209 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1209
       then
         let uu____1210 =
           let uu____1211 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1211 in
         let uu____1212 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1210 uu____1212
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1218 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1242 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1247 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1258 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1259 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1260 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1261 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1262 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1277 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1285 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1290 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1296 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1296 with
            | (e2,c,g) ->
                let g1 =
                  let uu___93_1307 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___93_1307.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___93_1307.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___93_1307.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1320 = FStar_Syntax_Util.type_u () in
           (match uu____1320 with
            | (t,u) ->
                let uu____1328 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1328 with
                 | (e2,c,g) ->
                     let uu____1338 =
                       let uu____1347 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1347 with
                       | (env2,uu____1360) -> tc_pats env2 pats in
                     (match uu____1338 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___94_1381 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___94_1381.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___94_1381.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___94_1381.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1382 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1389 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1382, c, uu____1389))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1397 =
             let uu____1398 = FStar_Syntax_Subst.compress e1 in
             uu____1398.FStar_Syntax_Syntax.n in
           (match uu____1397 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1404,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1406;
                               FStar_Syntax_Syntax.lbtyp = uu____1407;
                               FStar_Syntax_Syntax.lbeff = uu____1408;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1426 =
                  let uu____1430 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1430 e11 in
                (match uu____1426 with
                 | (e12,c1,g1) ->
                     let uu____1437 = tc_term env1 e2 in
                     (match uu____1437 with
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
                            let uu____1454 =
                              let uu____1457 =
                                let uu____1458 =
                                  let uu____1466 =
                                    let uu____1470 =
                                      let uu____1472 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1472] in
                                    (false, uu____1470) in
                                  (uu____1466, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1458 in
                              FStar_Syntax_Syntax.mk uu____1457 in
                            uu____1454
                              (Some
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
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1498 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1498)))
            | uu____1501 ->
                let uu____1502 = tc_term env1 e1 in
                (match uu____1502 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         (Some
                            ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                         top.FStar_Syntax_Syntax.pos in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1522) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1537 = tc_term env1 e1 in
           (match uu____1537 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1559) ->
           let uu____1595 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1595 with
            | (env0,uu____1603) ->
                let uu____1606 = tc_comp env0 expected_c in
                (match uu____1606 with
                 | (expected_c1,uu____1614,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1619 =
                       let uu____1623 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1623 e1 in
                     (match uu____1619 with
                      | (e2,c',g') ->
                          let uu____1630 =
                            let uu____1634 =
                              let uu____1637 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____1637) in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1634 in
                          (match uu____1630 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3, ((FStar_Util.Inl t_res), None),
                                        (Some
                                           (FStar_Syntax_Util.comp_effect_name
                                              expected_c2))))
                                   (Some (t_res.FStar_Syntax_Syntax.n))
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2 in
                               let f =
                                 let uu____1684 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1684 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | None  -> f
                                 | Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic) in
                               let uu____1689 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1689 with
                                | (e5,c,f2) ->
                                    let uu____1699 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____1699))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1703) ->
           let uu____1739 = FStar_Syntax_Util.type_u () in
           (match uu____1739 with
            | (k,u) ->
                let uu____1747 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1747 with
                 | (t1,uu____1755,f) ->
                     let uu____1757 =
                       let uu____1761 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1761 e1 in
                     (match uu____1757 with
                      | (e2,c,g) ->
                          let uu____1768 =
                            let uu____1771 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1775  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1771 e2 c f in
                          (match uu____1768 with
                           | (c1,f1) ->
                               let uu____1781 =
                                 let uu____1785 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2, ((FStar_Util.Inl t1), None),
                                          (Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____1785 c1 in
                               (match uu____1781 with
                                | (e3,c2,f2) ->
                                    let uu____1817 =
                                      let uu____1818 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1818 in
                                    (e3, c2, uu____1817))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1819;
              FStar_Syntax_Syntax.pos = uu____1820;
              FStar_Syntax_Syntax.vars = uu____1821;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1865 = FStar_Syntax_Util.head_and_args top in
           (match uu____1865 with
            | (unary_op,uu____1879) ->
                let head1 =
                  let uu____1897 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) None
                    uu____1897 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1)) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____1933);
              FStar_Syntax_Syntax.tk = uu____1934;
              FStar_Syntax_Syntax.pos = uu____1935;
              FStar_Syntax_Syntax.vars = uu____1936;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1980 = FStar_Syntax_Util.head_and_args top in
           (match uu____1980 with
            | (unary_op,uu____1994) ->
                let head1 =
                  let uu____2012 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) None
                    uu____2012 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1)) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____2048;
              FStar_Syntax_Syntax.pos = uu____2049;
              FStar_Syntax_Syntax.vars = uu____2050;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2076 =
               let uu____2080 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____2080 with | (env0,uu____2088) -> tc_term env0 e1 in
             match uu____2076 with
             | (e2,c,g) ->
                 let uu____2097 = FStar_Syntax_Util.head_and_args top in
                 (match uu____2097 with
                  | (reify_op,uu____2111) ->
                      let u_c =
                        let uu____2127 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____2127 with
                        | (uu____2131,c',uu____2133) ->
                            let uu____2134 =
                              let uu____2135 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____2135.FStar_Syntax_Syntax.n in
                            (match uu____2134 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2139 ->
                                 let uu____2140 = FStar_Syntax_Util.type_u () in
                                 (match uu____2140 with
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
                                            let uu____2149 =
                                              let uu____2150 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2151 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2152 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2150 uu____2151
                                                uu____2152 in
                                            failwith uu____2149);
                                       u))) in
                      let repr =
                        let uu____2154 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2154 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2172 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2172
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2173 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2173 with
                       | (e4,c2,g') ->
                           let uu____2183 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2183)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2185;
              FStar_Syntax_Syntax.pos = uu____2186;
              FStar_Syntax_Syntax.vars = uu____2187;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2219 =
               let uu____2220 =
                 let uu____2221 =
                   let uu____2224 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2224, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2221 in
               raise uu____2220 in
             let uu____2228 = FStar_Syntax_Util.head_and_args top in
             match uu____2228 with
             | (reflect_op,uu____2242) ->
                 let uu____2257 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2257 with
                  | None  -> no_reflect ()
                  | Some (ed,qualifiers) ->
                      let uu____2275 =
                        let uu____2276 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2276 in
                      if uu____2275
                      then no_reflect ()
                      else
                        (let uu____2282 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2282 with
                         | (env_no_ex,topt) ->
                             let uu____2293 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2308 =
                                   let uu____2311 =
                                     let uu____2312 =
                                       let uu____2322 =
                                         let uu____2324 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2325 =
                                           let uu____2327 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2327] in
                                         uu____2324 :: uu____2325 in
                                       (repr, uu____2322) in
                                     FStar_Syntax_Syntax.Tm_app uu____2312 in
                                   FStar_Syntax_Syntax.mk uu____2311 in
                                 uu____2308 None top.FStar_Syntax_Syntax.pos in
                               let uu____2337 =
                                 let uu____2341 =
                                   let uu____2342 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2342
                                     FStar_Pervasives.fst in
                                 tc_tot_or_gtot_term uu____2341 t in
                               match uu____2337 with
                               | (t1,uu____2359,g) ->
                                   let uu____2361 =
                                     let uu____2362 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2362.FStar_Syntax_Syntax.n in
                                   (match uu____2361 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2373,(res,uu____2375)::
                                         (wp,uu____2377)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2411 -> failwith "Impossible") in
                             (match uu____2293 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2435 =
                                    let uu____2438 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2438 with
                                    | (e2,c,g) ->
                                        ((let uu____2448 =
                                            let uu____2449 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2449 in
                                          if uu____2448
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2455 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2455 with
                                          | None  ->
                                              ((let uu____2460 =
                                                  let uu____2464 =
                                                    let uu____2467 =
                                                      let uu____2468 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2469 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2468 uu____2469 in
                                                    (uu____2467,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2464] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2460);
                                               (let uu____2474 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2474)))
                                          | Some g' ->
                                              let uu____2476 =
                                                let uu____2477 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2477 in
                                              (e2, uu____2476))) in
                                  (match uu____2435 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2484 =
                                           let uu____2485 =
                                             let uu____2486 =
                                               let uu____2487 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2487] in
                                             let uu____2488 =
                                               let uu____2494 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2494] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2486;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2488;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2485 in
                                         FStar_All.pipe_right uu____2484
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2511 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2511 with
                                        | (e4,c1,g') ->
                                            let uu____2521 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2521))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2540 =
               let uu____2541 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2541 FStar_Pervasives.fst in
             FStar_All.pipe_right uu____2540 instantiate_both in
           ((let uu____2550 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2550
             then
               let uu____2551 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2552 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2551
                 uu____2552
             else ());
            (let uu____2554 = tc_term (no_inst env2) head1 in
             match uu____2554 with
             | (head2,chead,g_head) ->
                 let uu____2564 =
                   let uu____2568 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2568
                   then
                     let uu____2572 =
                       let uu____2576 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____2576 in
                     match uu____2572 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____2585 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____2587 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____2587))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____2585
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let uu____2590 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env2 head2 chead g_head args
                        uu____2590) in
                 (match uu____2564 with
                  | (e1,c,g) ->
                      ((let uu____2599 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2599
                        then
                          let uu____2600 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2600
                        else ());
                       (let uu____2602 = comp_check_expected_typ env0 e1 c in
                        match uu____2602 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____2613 =
                                let uu____2614 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2614.FStar_Syntax_Syntax.n in
                              match uu____2613 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2618) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___95_2658 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___95_2658.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___95_2658.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___95_2658.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2687 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2689 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2689 in
                            ((let uu____2691 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2691
                              then
                                let uu____2692 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2693 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2692 uu____2693
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2721 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2721 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2733 = tc_term env12 e1 in
                (match uu____2733 with
                 | (e11,c1,g1) ->
                     let uu____2743 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2749 = FStar_Syntax_Util.type_u () in
                           (match uu____2749 with
                            | (k,uu____2755) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2757 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2757, res_t)) in
                     (match uu____2743 with
                      | (env_branches,res_t) ->
                          ((let uu____2764 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2764
                            then
                              let uu____2765 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2765
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2814 =
                              let uu____2817 =
                                FStar_List.fold_right
                                  (fun uu____2845  ->
                                     fun uu____2846  ->
                                       match (uu____2845, uu____2846) with
                                       | ((uu____2878,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2911 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____2911))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2817 with
                              | (cases,g) ->
                                  let uu____2932 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____2932, g) in
                            match uu____2814 with
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
                                           (fun uu____2993  ->
                                              match uu____2993 with
                                              | ((pat,wopt,br),uu____3009,lc,uu____3011)
                                                  ->
                                                  let uu____3018 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____3018))) in
                                    let e2 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_match
                                           (scrutinee, branches))
                                        (Some
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
                                             None),
                                           (Some
                                              (cres.FStar_Syntax_Syntax.eff_name))))
                                      None e3.FStar_Syntax_Syntax.pos in
                                  let uu____3066 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____3066
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____3073 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____3073 in
                                     let lb =
                                       let uu____3077 =
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
                                           uu____3077;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____3081 =
                                         let uu____3084 =
                                           let uu____3085 =
                                             let uu____3093 =
                                               let uu____3094 =
                                                 let uu____3095 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____3095] in
                                               FStar_Syntax_Subst.close
                                                 uu____3094 e_match in
                                             ((false, [lb]), uu____3093) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____3085 in
                                         FStar_Syntax_Syntax.mk uu____3084 in
                                       uu____3081
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____3109 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____3109
                                  then
                                    let uu____3110 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____3111 =
                                      let uu____3112 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____3112 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____3110 uu____3111
                                  else ());
                                 (let uu____3114 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____3114))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3117;
                FStar_Syntax_Syntax.lbunivs = uu____3118;
                FStar_Syntax_Syntax.lbtyp = uu____3119;
                FStar_Syntax_Syntax.lbeff = uu____3120;
                FStar_Syntax_Syntax.lbdef = uu____3121;_}::[]),uu____3122)
           ->
           ((let uu____3137 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3137
             then
               let uu____3138 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3138
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____3140),uu____3141) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3151;
                FStar_Syntax_Syntax.lbunivs = uu____3152;
                FStar_Syntax_Syntax.lbtyp = uu____3153;
                FStar_Syntax_Syntax.lbeff = uu____3154;
                FStar_Syntax_Syntax.lbdef = uu____3155;_}::uu____3156),uu____3157)
           ->
           ((let uu____3173 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3173
             then
               let uu____3174 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3174
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3176),uu____3177) ->
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
          let uu____3200 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3200 with
           | (tactic1,uu____3206,uu____3207) -> Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____3236 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3236 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3249 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3249
              then FStar_Util.Inl t1
              else
                (let uu____3253 =
                   let uu____3254 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3254 in
                 FStar_Util.Inr uu____3253) in
            let is_data_ctor uu___84_3263 =
              match uu___84_3263 with
              | Some (FStar_Syntax_Syntax.Data_ctor ) -> true
              | Some (FStar_Syntax_Syntax.Record_ctor uu____3265) -> true
              | uu____3269 -> false in
            let uu____3271 =
              (is_data_ctor dc) &&
                (let uu____3273 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3273) in
            if uu____3271
            then
              let uu____3277 =
                let uu____3278 =
                  let uu____3281 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3282 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3281, uu____3282) in
                FStar_Errors.Error uu____3278 in
              raise uu____3277
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3293 =
            let uu____3294 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3294 in
          failwith uu____3293
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3317 =
              let uu____3318 = FStar_Syntax_Subst.compress t1 in
              uu____3318.FStar_Syntax_Syntax.n in
            match uu____3317 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3321 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3329 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___96_3353 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___96_3353.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___96_3353.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___96_3353.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3385 =
            let uu____3392 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3392 with
            | None  ->
                let uu____3400 = FStar_Syntax_Util.type_u () in
                (match uu____3400 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3385 with
           | (t,uu____3421,g0) ->
               let uu____3429 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3429 with
                | (e1,uu____3440,g1) ->
                    let uu____3448 =
                      let uu____3449 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3449
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3450 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3448, uu____3450)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3452 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3461 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3461)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3452 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___97_3477 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___97_3477.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___97_3477.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3480 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3480 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3493 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3493
                       then FStar_Util.Inl t1
                       else
                         (let uu____3497 =
                            let uu____3498 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3498 in
                          FStar_Util.Inr uu____3497) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3504;
             FStar_Syntax_Syntax.pos = uu____3505;
             FStar_Syntax_Syntax.vars = uu____3506;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3514 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3514 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3532 =
                     let uu____3533 =
                       let uu____3536 =
                         let uu____3537 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____3538 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____3542 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____3537 uu____3538 uu____3542 in
                       let uu____3546 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____3536, uu____3546) in
                     FStar_Errors.Error uu____3533 in
                   raise uu____3532)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____3558 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____3562 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3562 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3568 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3568 with
           | ((us,t),range) ->
               ((let uu____3582 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3582
                 then
                   let uu____3583 =
                     let uu____3584 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3584 in
                   let uu____3585 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3586 = FStar_Range.string_of_range range in
                   let uu____3587 = FStar_Range.string_of_use_range range in
                   let uu____3588 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____3583 uu____3585 uu____3586 uu____3587 uu____3588
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____3593 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3593 us in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____3619 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3619 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3628 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3628 with
                | (env2,uu____3636) ->
                    let uu____3639 = tc_binders env2 bs1 in
                    (match uu____3639 with
                     | (bs2,env3,g,us) ->
                         let uu____3651 = tc_comp env3 c1 in
                         (match uu____3651 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___98_3664 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___98_3664.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___98_3664.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___98_3664.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u) None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____3681 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3681 in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              None top.FStar_Syntax_Syntax.pos in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____3708 =
            let uu____3711 =
              let uu____3712 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3712] in
            FStar_Syntax_Subst.open_term uu____3711 phi in
          (match uu____3708 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____3719 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3719 with
                | (env2,uu____3727) ->
                    let uu____3730 =
                      let uu____3737 = FStar_List.hd x1 in
                      tc_binder env2 uu____3737 in
                    (match uu____3730 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3754 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____3754
                           then
                             let uu____3755 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____3756 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____3757 =
                               FStar_Syntax_Print.bv_to_string (fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3755 uu____3756 uu____3757
                           else ());
                          (let uu____3759 = FStar_Syntax_Util.type_u () in
                           match uu____3759 with
                           | (t_phi,uu____3766) ->
                               let uu____3767 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____3767 with
                                | (phi2,uu____3775,f2) ->
                                    let e1 =
                                      let uu___99_3780 =
                                        FStar_Syntax_Util.refine (fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___99_3780.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___99_3780.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___99_3780.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u) None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____3795 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3795 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3804) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____3829 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____3829
            then
              let uu____3830 =
                FStar_Syntax_Print.term_to_string
                  (let uu___100_3833 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___100_3833.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___100_3833.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___100_3833.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3830
            else ());
           (let uu____3852 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____3852 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3860 ->
          let uu____3861 =
            let uu____3862 = FStar_Syntax_Print.term_to_string top in
            let uu____3863 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3862
              uu____3863 in
          failwith uu____3861
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3869 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3870,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3876,Some uu____3877) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3885 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3889 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3890 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3891 ->
          FStar_TypeChecker_Common.t_range
      | uu____3892 -> raise (FStar_Errors.Error ("Unsupported constant", r))
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
      | FStar_Syntax_Syntax.Total (t,uu____3903) ->
          let uu____3910 = FStar_Syntax_Util.type_u () in
          (match uu____3910 with
           | (k,u) ->
               let uu____3918 = tc_check_tot_or_gtot_term env t k in
               (match uu____3918 with
                | (t1,uu____3926,g) ->
                    let uu____3928 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____3928, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3930) ->
          let uu____3937 = FStar_Syntax_Util.type_u () in
          (match uu____3937 with
           | (k,u) ->
               let uu____3945 = tc_check_tot_or_gtot_term env t k in
               (match uu____3945 with
                | (t1,uu____3953,g) ->
                    let uu____3955 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____3955, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant None in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us)) None
                  c0.FStar_Syntax_Syntax.pos in
          let tc =
            let uu____3967 =
              let uu____3968 =
                let uu____3969 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____3969 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____3968 in
            uu____3967 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____3974 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____3974 with
           | (tc1,uu____3982,f) ->
               let uu____3984 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____3984 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4014 =
                        let uu____4015 = FStar_Syntax_Subst.compress head3 in
                        uu____4015.FStar_Syntax_Syntax.n in
                      match uu____4014 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4018,us) -> us
                      | uu____4024 -> [] in
                    let uu____4025 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____4025 with
                     | (uu____4038,args1) ->
                         let uu____4054 =
                           let uu____4066 = FStar_List.hd args1 in
                           let uu____4075 = FStar_List.tl args1 in
                           (uu____4066, uu____4075) in
                         (match uu____4054 with
                          | (res,args2) ->
                              let uu____4117 =
                                let uu____4122 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___85_4141  ->
                                          match uu___85_4141 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4147 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4147 with
                                               | (env1,uu____4154) ->
                                                   let uu____4157 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4157 with
                                                    | (e1,uu____4164,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____4122
                                  FStar_List.unzip in
                              (match uu____4117 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___101_4189 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___101_4189.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___101_4189.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4193 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4193 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____4196 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4196))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4204 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4205 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4211 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4211
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4214 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4214
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4218 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4218 FStar_Pervasives.snd
         | uu____4223 -> aux u)
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
            let uu____4244 =
              let uu____4245 =
                let uu____4248 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4248, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4245 in
            raise uu____4244 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4302 bs2 bs_expected1 =
              match uu____4302 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit
                            uu____4393)) ->
                             let uu____4396 =
                               let uu____4397 =
                                 let uu____4400 =
                                   let uu____4401 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4401 in
                                 let uu____4402 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4400, uu____4402) in
                               FStar_Errors.Error uu____4397 in
                             raise uu____4396
                         | (Some (FStar_Syntax_Syntax.Implicit
                            uu____4403),None ) ->
                             let uu____4406 =
                               let uu____4407 =
                                 let uu____4410 =
                                   let uu____4411 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4411 in
                                 let uu____4412 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4410, uu____4412) in
                               FStar_Errors.Error uu____4407 in
                             raise uu____4406
                         | uu____4413 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4417 =
                           let uu____4420 =
                             let uu____4421 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4421.FStar_Syntax_Syntax.n in
                           match uu____4420 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4426 ->
                               ((let uu____4428 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4428
                                 then
                                   let uu____4429 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4429
                                 else ());
                                (let uu____4431 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4431 with
                                 | (t,uu____4438,g1) ->
                                     let g2 =
                                       let uu____4441 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4442 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4441
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4442 in
                                     let g3 =
                                       let uu____4444 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4444 in
                                     (t, g3))) in
                         match uu____4417 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___102_4460 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___102_4460.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___102_4460.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4469 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4469 in
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
                  | uu____4558 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4562 = tc_binders env1 bs in
                  match uu____4562 with
                  | (bs1,envbody,g,uu____4583) ->
                      let uu____4584 =
                        let uu____4591 =
                          let uu____4592 = FStar_Syntax_Subst.compress body1 in
                          uu____4592.FStar_Syntax_Syntax.n in
                        match uu____4591 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4604) ->
                            let uu____4640 = tc_comp envbody c in
                            (match uu____4640 with
                             | (c1,uu____4651,g') ->
                                 let uu____4653 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4655 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), uu____4653, body1, uu____4655))
                        | uu____4658 -> (None, None, body1, g) in
                      (match uu____4584 with
                       | (copt,tacopt,body2,g1) ->
                           (None, bs1, [], copt, tacopt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____4717 =
                    let uu____4718 = FStar_Syntax_Subst.compress t2 in
                    uu____4718.FStar_Syntax_Syntax.n in
                  match uu____4717 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____4735 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4749 -> failwith "Impossible");
                       (let uu____4753 = tc_binders env1 bs in
                        match uu____4753 with
                        | (bs1,envbody,g,uu____4775) ->
                            let uu____4776 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4776 with
                             | (envbody1,uu____4795) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____4806;
                         FStar_Syntax_Syntax.tk = uu____4807;
                         FStar_Syntax_Syntax.pos = uu____4808;
                         FStar_Syntax_Syntax.vars = uu____4809;_},uu____4810)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4838 -> failwith "Impossible");
                       (let uu____4842 = tc_binders env1 bs in
                        match uu____4842 with
                        | (bs1,envbody,g,uu____4864) ->
                            let uu____4865 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4865 with
                             | (envbody1,uu____4884) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4896) ->
                      let uu____4901 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____4901 with
                       | (uu____4930,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4970 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____4970 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5033 c_expected2 =
                               match uu____5033 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____5094 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____5094)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____5111 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5111 in
                                        let uu____5112 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____5112)
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
                                               let uu____5153 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____5153 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5165 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____5165 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5192 =
                                                           let uu____5208 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____5208,
                                                             subst2) in
                                                         handle_more
                                                           uu____5192
                                                           c_expected4))
                                           | uu____5217 ->
                                               let uu____5218 =
                                                 let uu____5219 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____5219 in
                                               fail uu____5218 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____5235 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5235 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___103_5273 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___103_5273.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___103_5273.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___103_5273.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___103_5273.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___103_5273.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___103_5273.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___103_5273.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___103_5273.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___103_5273.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___103_5273.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___103_5273.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___103_5273.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___103_5273.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___103_5273.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___103_5273.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___103_5273.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___103_5273.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___103_5273.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___103_5273.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___103_5273.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___103_5273.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___103_5273.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___103_5273.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5299  ->
                                     fun uu____5300  ->
                                       match (uu____5299, uu____5300) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5325 =
                                             let uu____5329 =
                                               let uu____5330 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5330
                                                 FStar_Pervasives.fst in
                                             tc_term uu____5329 t3 in
                                           (match uu____5325 with
                                            | (t4,uu____5342,uu____5343) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5350 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___104_5353
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___104_5353.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___104_5353.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5350 ::
                                                        letrec_binders
                                                  | uu____5354 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5357 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5357 with
                            | (envbody,bs1,g,c) ->
                                let uu____5389 =
                                  let uu____5393 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5393
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5389 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), None, envbody2, body1, g))))
                  | uu____5429 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5444 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5444
                      else
                        (let uu____5446 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5446 with
                         | (uu____5474,bs1,uu____5476,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, tacopt,
                               envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5501 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5501 with
          | (env1,topt) ->
              ((let uu____5513 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5513
                then
                  let uu____5514 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5514
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5518 = expected_function_typ1 env1 topt body in
                match uu____5518 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5553 =
                      tc_term
                        (let uu___105_5559 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___105_5559.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___105_5559.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___105_5559.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___105_5559.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___105_5559.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___105_5559.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___105_5559.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___105_5559.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___105_5559.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___105_5559.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___105_5559.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___105_5559.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___105_5559.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___105_5559.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___105_5559.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___105_5559.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___105_5559.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___105_5559.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___105_5559.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___105_5559.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___105_5559.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___105_5559.FStar_TypeChecker_Env.qname_and_index)
                         }) body1 in
                    (match uu____5553 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5568 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5568
                           then
                             let uu____5569 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5578 =
                               let uu____5579 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5579 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5569 uu____5578
                           else ());
                          (let uu____5581 =
                             let uu____5585 =
                               let uu____5588 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5588) in
                             check_expected_effect
                               (let uu___106_5595 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___106_5595.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___106_5595.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___106_5595.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___106_5595.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___106_5595.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___106_5595.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___106_5595.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___106_5595.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___106_5595.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___106_5595.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___106_5595.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___106_5595.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___106_5595.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___106_5595.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___106_5595.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___106_5595.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___106_5595.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___106_5595.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___106_5595.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___106_5595.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___106_5595.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___106_5595.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___106_5595.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5585 in
                           match uu____5581 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____5604 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5606 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5606) in
                                 if uu____5604
                                 then
                                   let uu____5607 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5607
                                 else
                                   (let guard2 =
                                      let uu____5610 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5610 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 let uu____5617 =
                                   let uu____5624 =
                                     let uu____5630 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     FStar_All.pipe_right uu____5630
                                       (fun _0_30  -> FStar_Util.Inl _0_30) in
                                   Some uu____5624 in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5617 in
                               let uu____5644 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5659 -> (e, t1, guard2)
                                      | uu____5667 ->
                                          let uu____5668 =
                                            if use_teq
                                            then
                                              let uu____5673 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5673)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5668 with
                                           | (e1,guard') ->
                                               let uu____5680 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5680)))
                                 | None  -> (e, tfun_computed, guard2) in
                               (match uu____5644 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____5693 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____5693 with
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
              (let uu____5729 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____5729
               then
                 let uu____5730 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____5731 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5730
                   uu____5731
               else ());
              (let monadic_application uu____5769 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____5769 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___107_5806 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___107_5806.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___107_5806.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___107_5806.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____5807 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____5816 ->
                           let g =
                             let uu____5821 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____5821
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____5822 =
                             let uu____5823 =
                               let uu____5826 =
                                 let uu____5827 =
                                   let uu____5828 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____5828 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5827 in
                               FStar_Syntax_Syntax.mk_Total uu____5826 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5823 in
                           (uu____5822, g) in
                     (match uu____5807 with
                      | (cres2,guard1) ->
                          ((let uu____5839 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____5839
                            then
                              let uu____5840 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5840
                            else ());
                           (let cres3 =
                              let uu____5843 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____5843
                              then
                                let term =
                                  FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets_rev) None
                                    head2.FStar_Syntax_Syntax.pos in
                                FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                  env term cres2
                              else cres2 in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____5871  ->
                                     match uu____5871 with
                                     | ((e,q),x,c) ->
                                         let uu____5894 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____5894
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
                              let uu____5903 =
                                let uu____5904 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____5904.FStar_Syntax_Syntax.n in
                              match uu____5903 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____5908 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____5923  ->
                                         match uu____5923 with
                                         | (arg,uu____5931,uu____5932) -> arg
                                             :: args1) [] arg_comps_rev in
                                let app =
                                  FStar_Syntax_Syntax.mk_Tm_app head2 args1
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
                                (let uu____5942 =
                                   let map_fun uu____5977 =
                                     match uu____5977 with
                                     | ((e,q),uu____5997,c) ->
                                         let uu____6003 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6003
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
                                            let uu____6033 =
                                              let uu____6036 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____6036, q) in
                                            ((Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____6033)) in
                                   let uu____6054 =
                                     let uu____6068 =
                                       let uu____6081 =
                                         let uu____6089 =
                                           let uu____6094 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____6094, None, chead1) in
                                         uu____6089 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____6081 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6068 in
                                   match uu____6054 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6189 =
                                         let uu____6190 =
                                           FStar_List.hd reverse_args in
                                         fst uu____6190 in
                                       let uu____6195 =
                                         let uu____6199 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6199 in
                                       (lifted_args, uu____6189, uu____6195) in
                                 match uu____5942 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head3
                                         args1
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
                                     let bind_lifted_args e uu___86_6265 =
                                       match uu___86_6265 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6307 =
                                               let uu____6310 =
                                                 let uu____6311 =
                                                   let uu____6319 =
                                                     let uu____6320 =
                                                       let uu____6321 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6321] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6320 e in
                                                   ((false, [lb]),
                                                     uu____6319) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6311 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6310 in
                                             uu____6307 None
                                               e.FStar_Syntax_Syntax.pos in
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_meta
                                                (letbinding,
                                                  (FStar_Syntax_Syntax.Meta_monadic
                                                     (m,
                                                       (comp1.FStar_Syntax_Syntax.res_typ)))))
                                             None e.FStar_Syntax_Syntax.pos in
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args) in
                            let uu____6351 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6351 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6405 bs args1 =
                 match uu____6405 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6485))::rest,
                         (uu____6487,None )::uu____6488) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 = check_no_escape (Some head1) env fvs t in
                          let uu____6525 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6525 with
                           | (varg,uu____6536,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6549 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6549) in
                               let uu____6550 =
                                 let uu____6568 =
                                   let uu____6576 =
                                     let uu____6583 =
                                       let uu____6584 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____6584
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, None, uu____6583) in
                                   uu____6576 :: outargs in
                                 let uu____6594 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____6568, (arg :: arg_rets),
                                   uu____6594, fvs) in
                               tc_args head_info uu____6550 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit
                               uu____6654),Some (FStar_Syntax_Syntax.Implicit
                               uu____6655)) -> ()
                            | (None ,None ) -> ()
                            | (Some (FStar_Syntax_Syntax.Equality ),None ) ->
                                ()
                            | uu____6662 ->
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___108_6669 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___108_6669.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___108_6669.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6671 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6671
                             then
                               let uu____6672 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6672
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___109_6677 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___109_6677.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___109_6677.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___109_6677.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___109_6677.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___109_6677.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___109_6677.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___109_6677.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___109_6677.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___109_6677.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___109_6677.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___109_6677.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___109_6677.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___109_6677.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___109_6677.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___109_6677.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___109_6677.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___109_6677.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___109_6677.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___109_6677.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___109_6677.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___109_6677.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___109_6677.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___109_6677.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             (let uu____6679 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6679
                              then
                                let uu____6680 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6681 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6682 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6680 uu____6681 uu____6682
                              else ());
                             (let uu____6684 = tc_term env2 e in
                              match uu____6684 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____6701 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____6701 in
                                  let uu____6702 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____6702
                                  then
                                    let subst2 =
                                      let uu____6707 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6707 e1 in
                                    tc_args head_info
                                      (subst2, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        (x1 :: fvs)) rest rest'))))
                      | (uu____6755,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6776) ->
                          let uu____6806 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____6806 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6829 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____6829
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____6845 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____6845 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____6859 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____6859
                                            then
                                              let uu____6860 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____6860
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____6882 when Prims.op_Negation norm1 ->
                                     let uu____6883 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____6883
                                 | uu____6884 ->
                                     let uu____6885 =
                                       let uu____6886 =
                                         let uu____6889 =
                                           let uu____6890 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____6891 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6890 uu____6891 in
                                         let uu____6895 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____6889, uu____6895) in
                                       FStar_Errors.Error uu____6886 in
                                     raise uu____6885 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____6908 =
                   let uu____6909 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____6909.FStar_Syntax_Syntax.n in
                 match uu____6908 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____6917 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____6977 = tc_term env1 e in
                           (match uu____6977 with
                            | (e1,c,g_e) ->
                                let uu____6990 = tc_args1 env1 tl1 in
                                (match uu____6990 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7012 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7012))) in
                     let uu____7023 = tc_args1 env args in
                     (match uu____7023 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7045 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7068  ->
                                      match uu____7068 with
                                      | (uu____7076,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7045 in
                          let ml_or_tot t r1 =
                            let uu____7092 = FStar_Options.ml_ish () in
                            if uu____7092
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7095 =
                              let uu____7098 =
                                let uu____7099 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7099
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7098 in
                            ml_or_tot uu____7095 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7108 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7108
                            then
                              let uu____7109 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7110 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7111 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7109 uu____7110 uu____7111
                            else ());
                           (let uu____7114 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7114);
                           (let comp =
                              let uu____7116 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7125  ->
                                   fun out  ->
                                     match uu____7125 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7116 in
                            let uu____7134 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7139 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7134, comp, uu____7139))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7142;
                        FStar_Syntax_Syntax.tk = uu____7143;
                        FStar_Syntax_Syntax.pos = uu____7144;
                        FStar_Syntax_Syntax.vars = uu____7145;_},uu____7146)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7220 = tc_term env1 e in
                           (match uu____7220 with
                            | (e1,c,g_e) ->
                                let uu____7233 = tc_args1 env1 tl1 in
                                (match uu____7233 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7255 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7255))) in
                     let uu____7266 = tc_args1 env args in
                     (match uu____7266 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7288 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7311  ->
                                      match uu____7311 with
                                      | (uu____7319,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7288 in
                          let ml_or_tot t r1 =
                            let uu____7335 = FStar_Options.ml_ish () in
                            if uu____7335
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7338 =
                              let uu____7341 =
                                let uu____7342 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7342
                                  FStar_Pervasives.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7341 in
                            ml_or_tot uu____7338 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7351 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7351
                            then
                              let uu____7352 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7353 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7354 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7352 uu____7353 uu____7354
                            else ());
                           (let uu____7357 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7357);
                           (let comp =
                              let uu____7359 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7368  ->
                                   fun out  ->
                                     match uu____7368 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7359 in
                            let uu____7377 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7382 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7377, comp, uu____7382))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7397 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7397 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7433) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7439,uu____7440)
                     -> check_function_app t
                 | uu____7469 ->
                     let uu____7470 =
                       let uu____7471 =
                         let uu____7474 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7474, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7471 in
                     raise uu____7470 in
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
                  let uu____7525 =
                    FStar_List.fold_left2
                      (fun uu____7558  ->
                         fun uu____7559  ->
                           fun uu____7560  ->
                             match (uu____7558, uu____7559, uu____7560) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7604 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7604 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7616 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7616 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7620 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7620) &&
                                              (let uu____7622 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7622)) in
                                       let uu____7623 =
                                         let uu____7629 =
                                           let uu____7635 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7635] in
                                         FStar_List.append seen uu____7629 in
                                       let uu____7640 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7623, uu____7640, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7525 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           (Some (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____7667 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7667
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7669 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7669 with | (c2,g) -> (e, c2, g)))
              | uu____7681 ->
                  check_application_args env head1 chead g_head args
                    expected_topt
and tc_eqn:
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t*
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
        let uu____7702 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7702 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7726 = branch1 in
            (match uu____7726 with
             | (cpat,uu____7745,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7781 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____7781 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____7798 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____7798
                         then
                           let uu____7799 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____7800 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7799 uu____7800
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____7803 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____7803 with
                         | (env1,uu____7814) ->
                             let env11 =
                               let uu___110_7818 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___110_7818.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___110_7818.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___110_7818.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___110_7818.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___110_7818.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___110_7818.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___110_7818.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___110_7818.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___110_7818.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___110_7818.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___110_7818.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___110_7818.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___110_7818.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___110_7818.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___110_7818.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___110_7818.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___110_7818.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___110_7818.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___110_7818.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___110_7818.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___110_7818.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___110_7818.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___110_7818.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____7821 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____7821
                               then
                                 let uu____7822 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____7823 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____7822 uu____7823
                               else ());
                              (let uu____7825 = tc_tot_or_gtot_term env11 exp in
                               match uu____7825 with
                               | (exp1,lc,g) ->
                                   let g' =
                                     FStar_TypeChecker_Rel.teq env11
                                       lc.FStar_Syntax_Syntax.res_typ
                                       expected_pat_t in
                                   let g1 =
                                     FStar_TypeChecker_Rel.conj_guard g g' in
                                   let uu____7840 =
                                     let env12 =
                                       FStar_TypeChecker_Env.set_range env11
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let g2 =
                                       let uu___111_7843 = g1 in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___111_7843.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___111_7843.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___111_7843.FStar_TypeChecker_Env.implicits)
                                       } in
                                     let uu____7844 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env12 g2 in
                                     FStar_All.pipe_right uu____7844
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env11 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____7855 =
                                       let uu____7856 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____7856 in
                                     if uu____7855
                                     then
                                       let unresolved =
                                         let uu____7863 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____7863
                                           FStar_Util.set_elements in
                                       let uu____7877 =
                                         let uu____7878 =
                                           let uu____7881 =
                                             let uu____7882 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____7883 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____7884 =
                                               let uu____7885 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____7896  ->
                                                         match uu____7896
                                                         with
                                                         | (u,uu____7900) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____7885
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____7882 uu____7883
                                               uu____7884 in
                                           (uu____7881,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____7878 in
                                       raise uu____7877
                                     else ());
                                    (let uu____7904 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____7904
                                     then
                                       let uu____7905 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____7905
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____7913 =
                   let uu____7917 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____7917
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____7913 with
                  | (scrutinee_env,uu____7930) ->
                      let uu____7933 = tc_pat true pat_t pattern in
                      (match uu____7933 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____7955 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____7970 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____7970
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____7978 =
                                      let uu____7982 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____7982 e in
                                    match uu____7978 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____7955 with
                            | (when_clause1,g_when) ->
                                let uu____8002 = tc_term pat_env branch_exp in
                                (match uu____8002 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____8021 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_31  -> Some _0_31)
                                             uu____8021 in
                                     let uu____8023 =
                                       let eqs =
                                         let uu____8029 =
                                           let uu____8030 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____8030 in
                                         if uu____8029
                                         then None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____8035 -> None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8046 -> None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8047 -> None
                                            | uu____8048 ->
                                                let uu____8049 =
                                                  let uu____8050 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8050 pat_t
                                                    scrutinee_tm e in
                                                Some uu____8049) in
                                       let uu____8051 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____8051 with
                                       | (c1,g_branch1) ->
                                           let uu____8061 =
                                             match (eqs, when_condition) with
                                             | uu____8068 when
                                                 let uu____8073 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8073
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____8081 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8082 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8081, uu____8082)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____8089 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8089 in
                                                 let uu____8090 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8091 =
                                                   let uu____8092 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8092 g_when in
                                                 (uu____8090, uu____8091)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____8098 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8098, g_when) in
                                           (match uu____8061 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____8106 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____8107 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8106, uu____8107,
                                                  g_branch1)) in
                                     (match uu____8023 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8120 =
                                              let uu____8121 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8121 in
                                            if uu____8120
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8146 =
                                                     let uu____8147 =
                                                       let uu____8148 =
                                                         let uu____8150 =
                                                           let uu____8154 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8154 in
                                                         snd uu____8150 in
                                                       FStar_List.length
                                                         uu____8148 in
                                                     uu____8147 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8146
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____8159 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8159 with
                                                     | None  -> []
                                                     | uu____8170 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None in
                                                         let disc1 =
                                                           let uu____8180 =
                                                             let uu____8181 =
                                                               let uu____8182
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8182] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8181 in
                                                           uu____8180 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8187 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool in
                                                         [uu____8187]
                                                   else [] in
                                                 let fail uu____8192 =
                                                   let uu____8193 =
                                                     let uu____8194 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____8195 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____8196 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8194 uu____8195
                                                       uu____8196 in
                                                   failwith uu____8193 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8207) ->
                                                       head_constructor t1
                                                   | uu____8212 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____8214 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____8214
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____8216 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____8227;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8228;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8229;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8230;_},uu____8231)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8256 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____8258 =
                                                       let uu____8259 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8259
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____8258]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8260 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8266 =
                                                       let uu____8267 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8267 in
                                                     if uu____8266
                                                     then []
                                                     else
                                                       (let uu____8270 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8270)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8272 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8274 =
                                                       let uu____8275 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8275 in
                                                     if uu____8274
                                                     then []
                                                     else
                                                       (let uu____8278 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8278)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8297 =
                                                       let uu____8298 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8298 in
                                                     if uu____8297
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8303 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8325
                                                                     ->
                                                                    match uu____8325
                                                                    with
                                                                    | 
                                                                    (ei,uu____8332)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8338
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8338
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8349
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8358
                                                                    =
                                                                    let uu____8359
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None in
                                                                    let uu____8360
                                                                    =
                                                                    let uu____8361
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8361] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8359
                                                                    uu____8360 in
                                                                    uu____8358
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8303
                                                            FStar_List.flatten in
                                                        let uu____8369 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8369
                                                          sub_term_guards)
                                                 | uu____8371 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8383 =
                                                   let uu____8384 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8384 in
                                                 if uu____8383
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8387 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8387 in
                                                    let uu____8390 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8390 with
                                                    | (k,uu____8394) ->
                                                        let uu____8395 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8395
                                                         with
                                                         | (t1,uu____8400,uu____8401)
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
                                          ((let uu____8407 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8407
                                            then
                                              let uu____8408 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8408
                                            else ());
                                           (let uu____8410 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8410, branch_guard, c1,
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
          let uu____8428 = check_let_bound_def true env1 lb in
          (match uu____8428 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8442 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____8451 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____8451, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8454 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8454
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8457 =
                      let uu____8462 =
                        let uu____8468 =
                          let uu____8473 =
                            let uu____8481 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8481) in
                          [uu____8473] in
                        FStar_TypeChecker_Util.generalize env1 uu____8468 in
                      FStar_List.hd uu____8462 in
                    match uu____8457 with
                    | (uu____8510,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8442 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8521 =
                      let uu____8526 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8526
                      then
                        let uu____8531 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8531 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8548 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____8548
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8549 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     None e2.FStar_Syntax_Syntax.pos in
                                 (uu____8549, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8563 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8563
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8571 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8571
                            then e2
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta
                                   (e2,
                                     (FStar_Syntax_Syntax.Meta_desugared
                                        FStar_Syntax_Syntax.Masked_effect)))
                                None e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____8521 with
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
                           let uu____8599 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false, [lb1]), e21))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8599,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8614 -> failwith "Impossible"
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
            let uu___112_8635 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___112_8635.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___112_8635.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___112_8635.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___112_8635.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___112_8635.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___112_8635.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___112_8635.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___112_8635.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___112_8635.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___112_8635.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___112_8635.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___112_8635.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___112_8635.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___112_8635.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___112_8635.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___112_8635.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___112_8635.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___112_8635.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___112_8635.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___112_8635.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___112_8635.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___112_8635.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___112_8635.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____8636 =
            let uu____8642 =
              let uu____8643 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8643 FStar_Pervasives.fst in
            check_let_bound_def false uu____8642 lb in
          (match uu____8636 with
           | (e1,uu____8655,c1,g1,annotated) ->
               let x =
                 let uu___113_8660 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___113_8660.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___113_8660.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8661 =
                 let uu____8664 =
                   let uu____8665 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8665] in
                 FStar_Syntax_Subst.open_term uu____8664 e2 in
               (match uu____8661 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = fst xbinder in
                    let uu____8677 =
                      let uu____8681 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8681 e21 in
                    (match uu____8677 with
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
                           let uu____8696 =
                             let uu____8699 =
                               let uu____8700 =
                                 let uu____8708 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8708) in
                               FStar_Syntax_Syntax.Tm_let uu____8700 in
                             FStar_Syntax_Syntax.mk uu____8699 in
                           uu____8696
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____8723 =
                             let uu____8724 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____8725 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____8724
                               c1.FStar_Syntax_Syntax.res_typ uu____8725 e11 in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8723 in
                         let g21 =
                           let uu____8727 =
                             let uu____8728 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____8728 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____8727 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____8730 =
                           let uu____8731 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____8731 in
                         if uu____8730
                         then
                           let tt =
                             let uu____8737 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____8737 FStar_Option.get in
                           ((let uu____8741 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8741
                             then
                               let uu____8742 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____8743 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____8742 uu____8743
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____8748 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8748
                             then
                               let uu____8749 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____8750 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8749 uu____8750
                             else ());
                            (e4,
                              ((let uu___114_8753 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___114_8753.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___114_8753.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___114_8753.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8754 -> failwith "Impossible"
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
          let uu____8775 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8775 with
           | (lbs1,e21) ->
               let uu____8786 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8786 with
                | (env0,topt) ->
                    let uu____8797 = build_let_rec_env true env0 lbs1 in
                    (match uu____8797 with
                     | (lbs2,rec_env) ->
                         let uu____8808 = check_let_recs rec_env lbs2 in
                         (match uu____8808 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8820 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____8820
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____8824 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____8824
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
                                     let uu____8852 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____8876 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____8876))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8852 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____8901  ->
                                           match uu____8901 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____8926 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____8926 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____8935 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____8935 with
                                | (lbs5,e22) ->
                                    ((let uu____8947 =
                                        FStar_TypeChecker_Rel.discharge_guard
                                          env1 g_lbs1 in
                                      FStar_All.pipe_right uu____8947
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1));
                                     (let uu____8948 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs5), e22))
                                          (Some
                                             (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos in
                                      (uu____8948, cres,
                                        FStar_TypeChecker_Rel.trivial_guard)))))))))
      | uu____8961 -> failwith "Impossible"
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
          let uu____8982 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8982 with
           | (lbs1,e21) ->
               let uu____8993 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8993 with
                | (env0,topt) ->
                    let uu____9004 = build_let_rec_env false env0 lbs1 in
                    (match uu____9004 with
                     | (lbs2,rec_env) ->
                         let uu____9015 = check_let_recs rec_env lbs2 in
                         (match uu____9015 with
                          | (lbs3,g_lbs) ->
                              let uu____9026 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___115_9042 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___115_9042.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___115_9042.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___116_9044 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___116_9044.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___116_9044.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___116_9044.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___116_9044.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____9026 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____9062 = tc_term env2 e21 in
                                   (match uu____9062 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9073 =
                                            let uu____9074 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9074 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9073 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___117_9078 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___117_9078.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___117_9078.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___117_9078.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9079 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9079 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | Some uu____9104 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres in
                                                  let cres3 =
                                                    let uu___118_9109 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___118_9109.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___118_9109.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___118_9109.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9112 -> failwith "Impossible"
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
          let uu____9135 =
            let uu____9138 =
              let uu____9139 = FStar_Syntax_Subst.compress t in
              uu____9139.FStar_Syntax_Syntax.n in
            let uu____9142 =
              let uu____9143 = FStar_Syntax_Subst.compress lbdef in
              uu____9143.FStar_Syntax_Syntax.n in
            (uu____9138, uu____9142) in
          match uu____9135 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9149,uu____9150)) ->
              let actuals1 =
                let uu____9184 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9184
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____9202 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9202) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____9214 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____9214) in
                  let msg =
                    let uu____9219 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____9220 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9219 uu____9220 formals_msg actuals_msg in
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____9225 ->
              let uu____9228 =
                let uu____9229 =
                  let uu____9232 =
                    let uu____9233 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____9234 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9233 uu____9234 in
                  (uu____9232, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____9229 in
              raise uu____9228 in
        let uu____9235 =
          FStar_List.fold_left
            (fun uu____9255  ->
               fun lb  ->
                 match uu____9255 with
                 | (lbs1,env1) ->
                     let uu____9267 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9267 with
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
                              (let uu____9281 =
                                 let uu____9285 =
                                   let uu____9286 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left FStar_Pervasives.fst
                                     uu____9286 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___119_9293 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___119_9293.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___119_9293.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___119_9293.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___119_9293.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___119_9293.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___119_9293.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___119_9293.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___119_9293.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___119_9293.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___119_9293.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___119_9293.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___119_9293.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___119_9293.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___119_9293.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___119_9293.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___119_9293.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___119_9293.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___119_9293.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___119_9293.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___119_9293.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___119_9293.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___119_9293.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___119_9293.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____9285 in
                               match uu____9281 with
                               | (t1,uu____9295,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9299 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9299);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9301 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9301
                            then
                              let uu___120_9302 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___120_9302.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___120_9302.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___120_9302.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___120_9302.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___120_9302.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___120_9302.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___120_9302.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___120_9302.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___120_9302.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___120_9302.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___120_9302.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___120_9302.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___120_9302.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___120_9302.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___120_9302.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___120_9302.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___120_9302.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___120_9302.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___120_9302.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___120_9302.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___120_9302.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___120_9302.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___120_9302.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___121_9312 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___121_9312.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___121_9312.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9235 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9326 =
        let uu____9331 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9351 =
                     let uu____9352 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____9352.FStar_Syntax_Syntax.n in
                   match uu____9351 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9355 -> ()
                   | uu____9370 ->
                       let uu____9371 =
                         let uu____9372 =
                           let uu____9375 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____9375) in
                         FStar_Errors.Error uu____9372 in
                       raise uu____9371);
                  (let uu____9376 =
                     let uu____9380 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____9380
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____9376 with
                   | (e,c,g) ->
                       ((let uu____9387 =
                           let uu____9388 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____9388 in
                         if uu____9387
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
        FStar_All.pipe_right uu____9331 FStar_List.unzip in
      match uu____9326 with
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
        let uu____9417 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9417 with
        | (env1,uu____9427) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9433 = check_lbtyp top_level env lb in
            (match uu____9433 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9460 =
                     tc_maybe_toplevel_term
                       (let uu___122_9466 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___122_9466.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___122_9466.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___122_9466.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___122_9466.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___122_9466.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___122_9466.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___122_9466.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___122_9466.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___122_9466.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___122_9466.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___122_9466.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___122_9466.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___122_9466.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___122_9466.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___122_9466.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___122_9466.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___122_9466.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___122_9466.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___122_9466.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___122_9466.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___122_9466.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___122_9466.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___122_9466.FStar_TypeChecker_Env.qname_and_index)
                        }) e11 in
                   match uu____9460 with
                   | (e12,c1,g1) ->
                       let uu____9475 =
                         let uu____9478 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9482  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9478 e12 c1 wf_annot in
                       (match uu____9475 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9492 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9492
                              then
                                let uu____9493 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9494 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9495 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9493 uu____9494 uu____9495
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
        | uu____9521 ->
            let uu____9522 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9522 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9549 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9549)
                 else
                   (let uu____9554 = FStar_Syntax_Util.type_u () in
                    match uu____9554 with
                    | (k,uu____9565) ->
                        let uu____9566 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9566 with
                         | (t2,uu____9578,g) ->
                             ((let uu____9581 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9581
                               then
                                 let uu____9582 =
                                   let uu____9583 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9583 in
                                 let uu____9584 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9582 uu____9584
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9587 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9587))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9592  ->
      match uu____9592 with
      | (x,imp) ->
          let uu____9603 = FStar_Syntax_Util.type_u () in
          (match uu____9603 with
           | (tu,u) ->
               ((let uu____9615 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9615
                 then
                   let uu____9616 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9617 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9618 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9616 uu____9617 uu____9618
                 else ());
                (let uu____9620 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9620 with
                 | (t,uu____9631,g) ->
                     let x1 =
                       ((let uu___123_9637 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___123_9637.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___123_9637.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9639 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9639
                       then
                         let uu____9640 =
                           FStar_Syntax_Print.bv_to_string (fst x1) in
                         let uu____9641 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9640 uu____9641
                       else ());
                      (let uu____9643 = push_binding env x1 in
                       (x1, uu____9643, g, u))))))
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
            let uu____9694 = tc_binder env1 b in
            (match uu____9694 with
             | (b1,env',g,u) ->
                 let uu____9717 = aux env' bs2 in
                 (match uu____9717 with
                  | (bs3,env'1,g',us) ->
                      let uu____9746 =
                        let uu____9747 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____9747 in
                      ((b1 :: bs3), env'1, uu____9746, (u :: us)))) in
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
          (fun uu____9801  ->
             fun uu____9802  ->
               match (uu____9801, uu____9802) with
               | ((t,imp),(args1,g)) ->
                   let uu____9839 = tc_term env1 t in
                   (match uu____9839 with
                    | (t1,uu____9849,g') ->
                        let uu____9851 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____9851))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9877  ->
             match uu____9877 with
             | (pats1,g) ->
                 let uu____9891 = tc_args env p in
                 (match uu____9891 with
                  | (args,g') ->
                      let uu____9899 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____9899))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____9907 = tc_maybe_toplevel_term env e in
      match uu____9907 with
      | (e1,c,g) ->
          let uu____9917 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____9917
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____9927 =
               let uu____9930 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____9930
               then
                 let uu____9933 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____9933, false)
               else
                 (let uu____9935 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____9935, true)) in
             match uu____9927 with
             | (target_comp,allow_ghost) ->
                 let uu____9941 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____9941 with
                  | Some g' ->
                      let uu____9947 = FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____9947)
                  | uu____9948 ->
                      if allow_ghost
                      then
                        let uu____9953 =
                          let uu____9954 =
                            let uu____9957 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____9957, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____9954 in
                        raise uu____9953
                      else
                        (let uu____9962 =
                           let uu____9963 =
                             let uu____9966 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____9966, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____9963 in
                         raise uu____9962)))
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
      let uu____9979 = tc_tot_or_gtot_term env t in
      match uu____9979 with
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
      (let uu____9999 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9999
       then
         let uu____10000 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____10000
       else ());
      (let env1 =
         let uu___124_10003 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___124_10003.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___124_10003.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___124_10003.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___124_10003.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___124_10003.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___124_10003.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___124_10003.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___124_10003.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___124_10003.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___124_10003.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___124_10003.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___124_10003.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___124_10003.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___124_10003.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___124_10003.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___124_10003.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___124_10003.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___124_10003.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___124_10003.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___124_10003.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___124_10003.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____10006 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10027) ->
             let uu____10028 =
               let uu____10029 =
                 let uu____10032 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____10032) in
               FStar_Errors.Error uu____10029 in
             raise uu____10028 in
       match uu____10006 with
       | (t,c,g) ->
           let uu____10042 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____10042
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10049 =
                let uu____10050 =
                  let uu____10053 =
                    let uu____10054 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10054 in
                  let uu____10055 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____10053, uu____10055) in
                FStar_Errors.Error uu____10050 in
              raise uu____10049))
let level_of_type_fail env e t =
  let uu____10076 =
    let uu____10077 =
      let uu____10080 =
        let uu____10081 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10081 t in
      let uu____10082 = FStar_TypeChecker_Env.get_range env in
      (uu____10080, uu____10082) in
    FStar_Errors.Error uu____10077 in
  raise uu____10076
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____10099 =
            let uu____10100 = FStar_Syntax_Util.unrefine t1 in
            uu____10100.FStar_Syntax_Syntax.n in
          match uu____10099 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10104 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____10107 = FStar_Syntax_Util.type_u () in
                 match uu____10107 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___127_10113 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___127_10113.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___127_10113.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___127_10113.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___127_10113.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___127_10113.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___127_10113.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___127_10113.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___127_10113.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___127_10113.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___127_10113.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___127_10113.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___127_10113.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___127_10113.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___127_10113.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___127_10113.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___127_10113.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___127_10113.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___127_10113.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___127_10113.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___127_10113.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___127_10113.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___127_10113.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___127_10113.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____10117 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____10117
                       | uu____10118 ->
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
      let uu____10127 =
        let uu____10128 = FStar_Syntax_Subst.compress e in
        uu____10128.FStar_Syntax_Syntax.n in
      match uu____10127 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10133 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10138 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10161 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10172) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10197,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10216) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10223 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10223 with | ((uu____10230,t),uu____10232) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10235,(FStar_Util.Inl t,uu____10237),uu____10238) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10274,(FStar_Util.Inr c,uu____10276),uu____10277) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)) None
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10320;
             FStar_Syntax_Syntax.pos = uu____10321;
             FStar_Syntax_Syntax.vars = uu____10322;_},us)
          ->
          let uu____10328 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10328 with
           | ((us',t),uu____10337) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10345 =
                     let uu____10346 =
                       let uu____10349 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10349) in
                     FStar_Errors.Error uu____10346 in
                   raise uu____10345)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10361 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10362 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10370) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10387 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10387 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10402  ->
                      match uu____10402 with
                      | (b,uu____10406) ->
                          let uu____10407 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10407) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10412 = universe_of_aux env res in
                 level_of_type env res uu____10412 in
               let u_c =
                 let uu____10414 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10414 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10417 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10417 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____10487 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10497 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10527 ->
                let uu____10528 = universe_of_aux env hd3 in
                (uu____10528, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10538 ->
                let uu____10539 = universe_of_aux env hd3 in
                (uu____10539, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10549 ->
                let uu____10560 = universe_of_aux env hd3 in
                (uu____10560, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10570 ->
                let uu____10575 = universe_of_aux env hd3 in
                (uu____10575, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10585 ->
                let uu____10603 = universe_of_aux env hd3 in
                (uu____10603, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10613 ->
                let uu____10618 = universe_of_aux env hd3 in
                (uu____10618, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10628 ->
                let uu____10629 = universe_of_aux env hd3 in
                (uu____10629, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10639 ->
                let uu____10647 = universe_of_aux env hd3 in
                (uu____10647, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____10657 ->
                let uu____10662 = universe_of_aux env hd3 in
                (uu____10662, args1)
            | FStar_Syntax_Syntax.Tm_type uu____10672 ->
                let uu____10673 = universe_of_aux env hd3 in
                (uu____10673, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10683,hd4::uu____10685) ->
                let uu____10728 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____10728 with
                 | (uu____10738,uu____10739,hd5) ->
                     let uu____10753 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____10753 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10788 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____10790 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____10790 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10825 ->
                let uu____10826 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____10826 with
                 | (env1,uu____10840) ->
                     let env2 =
                       let uu___128_10844 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___128_10844.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___128_10844.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___128_10844.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___128_10844.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___128_10844.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___128_10844.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___128_10844.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___128_10844.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___128_10844.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___128_10844.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___128_10844.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___128_10844.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___128_10844.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___128_10844.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___128_10844.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___128_10844.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___128_10844.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___128_10844.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___128_10844.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___128_10844.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___128_10844.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     ((let uu____10846 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____10846
                       then
                         let uu____10847 =
                           let uu____10848 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____10848 in
                         let uu____10849 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10847 uu____10849
                       else ());
                      (let uu____10851 = tc_term env2 hd3 in
                       match uu____10851 with
                       | (uu____10864,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10865;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10867;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10868;_},g)
                           ->
                           ((let uu____10878 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____10878
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____10886 = type_of_head true hd1 args in
          (match uu____10886 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____10915 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____10915 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____10948 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____10948)))
      | FStar_Syntax_Syntax.Tm_match (uu____10951,hd1::uu____10953) ->
          let uu____10996 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____10996 with
           | (uu____10999,uu____11000,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11014,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____11046 = universe_of_aux env e in
      level_of_type env e uu____11046
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____11059 = tc_binders env tps in
      match uu____11059 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))