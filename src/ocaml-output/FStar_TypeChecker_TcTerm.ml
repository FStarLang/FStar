open Prims
let instantiate_both : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___89_5 = env  in
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
  
let no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___90_10 = env  in
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
  
let mk_lex_list :
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
                 tl1.FStar_Syntax_Syntax.pos
              in
           let uu____37 =
             let uu____38 =
               let uu____39 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____40 =
                 let uu____42 = FStar_Syntax_Syntax.as_arg tl1  in [uu____42]
                  in
               uu____39 :: uu____40  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____38
              in
           uu____37 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)
      vs FStar_Syntax_Util.lex_top
  
let is_eq : FStar_Syntax_Syntax.arg_qualifier option -> Prims.bool =
  fun uu___84_51  ->
    match uu___84_51 with
    | Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____53 -> false
  
let steps env =
  [FStar_TypeChecker_Normalize.Beta;
  FStar_TypeChecker_Normalize.Eager_unfolding] 
let norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> FStar_TypeChecker_Normalize.normalize (steps env) env t
  
let norm_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
  
let check_no_escape :
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
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____114 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
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
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____124
                            | Some head1 ->
                                let uu____126 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____127 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____126 uu____127
                             in
                          let uu____128 =
                            let uu____129 =
                              let uu____132 =
                                FStar_TypeChecker_Env.get_range env  in
                              (msg, uu____132)  in
                            FStar_Errors.Error uu____129  in
                          raise uu____128  in
                        let s =
                          let uu____134 =
                            let uu____135 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives.fst
                              uu____135
                             in
                          FStar_TypeChecker_Util.new_uvar env uu____134  in
                        let uu____140 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s  in
                        match uu____140 with
                        | Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____144 -> fail ()))
             in
          aux false kt
  
let push_binding env b = FStar_TypeChecker_Env.push_bv env (fst b) 
let maybe_extend_subst :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.subst_t
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____181 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____181 then s else (FStar_Syntax_Syntax.NT ((fst b), v1)) :: s
  
let set_lcomp_result :
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___91_197 = lc  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___91_197.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___91_197.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____198  ->
             let uu____199 = lc.FStar_Syntax_Syntax.comp ()  in
             FStar_Syntax_Util.set_result_typ uu____199 t)
      }
  
let memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun t  ->
      FStar_ST.write e.FStar_Syntax_Syntax.tk
        (Some (t.FStar_Syntax_Syntax.n));
      e
  
let value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          let should_return t =
            let uu____244 =
              let uu____245 = FStar_Syntax_Subst.compress t  in
              uu____245.FStar_Syntax_Syntax.n  in
            match uu____244 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____248,c) ->
                let uu____260 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                if uu____260
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c)
                     in
                  let uu____262 =
                    let uu____263 = FStar_Syntax_Subst.compress t1  in
                    uu____263.FStar_Syntax_Syntax.n  in
                  (match uu____262 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____267 -> false
                   | uu____268 -> true)
                else false
            | uu____270 -> true  in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____273 =
                  let uu____276 =
                    (let uu____277 = should_return t  in
                     Prims.op_Negation uu____277) ||
                      (let uu____278 =
                         FStar_TypeChecker_Env.should_verify env  in
                       Prims.op_Negation uu____278)
                     in
                  if uu____276
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e  in
                FStar_Syntax_Util.lcomp_of_comp uu____273
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____286 =
            let uu____290 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____290 with
            | None  -> let uu____295 = memo_tk e t  in (uu____295, lc, guard)
            | Some t' ->
                ((let uu____298 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High  in
                  if uu____298
                  then
                    let uu____299 = FStar_Syntax_Print.term_to_string t  in
                    let uu____300 = FStar_Syntax_Print.term_to_string t'  in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____299
                      uu____300
                  else ());
                 (let uu____302 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t'
                     in
                  match uu____302 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                      let uu____313 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____313 with
                       | (e2,g) ->
                           ((let uu____322 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____322
                             then
                               let uu____323 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____324 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____325 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____326 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____323 uu____324 uu____325 uu____326
                             else ());
                            (let msg =
                               let uu____332 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               if uu____332
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_39  -> Some _0_39)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             let uu____347 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1
                                in
                             match uu____347 with
                             | (lc2,g2) ->
                                 let uu____355 = memo_tk e2 t'  in
                                 (uu____355, (set_lcomp_result lc2 t'), g2))))))
             in
          match uu____286 with
          | (e1,lc1,g) ->
              ((let uu____363 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                if uu____363
                then
                  let uu____364 = FStar_Syntax_Print.lcomp_to_string lc1  in
                  FStar_Util.print1 "Return comp type is %s\n" uu____364
                else ());
               (e1, lc1, g))
  
let comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____384 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____384 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____390 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____390 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
  
let check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun copt  ->
      fun uu____415  ->
        match uu____415 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____435 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____435
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____437 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____437
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
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
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____449))
                     in
                  if uu____448
                  then
                    let uu____453 =
                      let uu____455 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      Some uu____455  in
                    (uu____453, c)
                  else
                    (let uu____458 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____458
                     then let uu____462 = tot_or_gtot c  in (None, uu____462)
                     else
                       (let uu____465 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____465
                        then
                          let uu____469 =
                            let uu____471 = tot_or_gtot c  in Some uu____471
                             in
                          (uu____469, c)
                        else (None, c)))
               in
            (match uu____439 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | None  -> (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | Some expected_c ->
                      let uu____487 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c
                         in
                      (match uu____487 with
                       | (e1,uu____495,g) ->
                           let g1 =
                             let uu____498 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_TypeChecker_Util.label_guard uu____498
                               "could not prove post-condition" g
                              in
                           ((let uu____500 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low
                                in
                             if uu____500
                             then
                               let uu____501 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____502 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1
                                  in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____501 uu____502
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2)
                                in
                             (e2, expected_c, g1))))))
  
let no_logical_guard env uu____528 =
  match uu____528 with
  | (te,kt,f) ->
      let uu____535 = FStar_TypeChecker_Rel.guard_form f  in
      (match uu____535 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____540 =
             let uu____541 =
               let uu____544 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____545 = FStar_TypeChecker_Env.get_range env  in
               (uu____544, uu____545)  in
             FStar_Errors.Error uu____541  in
           raise uu____540)
  
let print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____553 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____553 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____556 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____556
  
let check_smt_pat env t bs c =
  let uu____597 = FStar_Syntax_Util.is_smt_lemma t  in
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
              [FStar_TypeChecker_Normalize.Beta] env pats
             in
          FStar_Syntax_Free.names uu____639  in
        let uu____640 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____652  ->
                  match uu____652 with
                  | (b,uu____656) ->
                      let uu____657 = FStar_Util.set_mem b pat_vars  in
                      Prims.op_Negation uu____657))
           in
        (match uu____640 with
         | None  -> ()
         | Some (x,uu____661) ->
             let uu____664 =
               let uu____665 = FStar_Syntax_Print.bv_to_string x  in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____665
                in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____664)
    | uu____666 -> failwith "Impossible"
  else () 
let guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____690 =
          let uu____691 = FStar_TypeChecker_Env.should_verify env  in
          Prims.op_Negation uu____691  in
        if uu____690
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env  in
               let env1 =
                 let uu___92_709 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___92_709.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___92_709.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___92_709.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___92_709.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___92_709.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___92_709.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___92_709.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___92_709.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___92_709.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___92_709.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___92_709.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___92_709.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___92_709.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___92_709.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___92_709.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___92_709.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___92_709.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___92_709.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___92_709.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___92_709.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___92_709.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___92_709.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___92_709.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___92_709.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___92_709.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___92_709.FStar_TypeChecker_Env.is_native_tactic)
                 }  in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid
                  in
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
                                     b.FStar_Syntax_Syntax.sort
                                    in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____739
                                  in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____741 -> []
                                | FStar_Syntax_Syntax.Tm_arrow uu____742 ->
                                    []
                                | uu____750 ->
                                    let uu____751 =
                                      FStar_Syntax_Syntax.bv_to_name b  in
                                    [uu____751])))
                    in
                 let as_lex_list dec =
                   let uu____756 = FStar_Syntax_Util.head_and_args dec  in
                   match uu____756 with
                   | (head1,uu____767) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____783 -> mk_lex_list [dec])
                    in
                 let cflags = FStar_Syntax_Util.comp_flags c  in
                 let uu____786 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___85_790  ->
                           match uu___85_790 with
                           | FStar_Syntax_Syntax.DECREASES uu____791 -> true
                           | uu____794 -> false))
                    in
                 match uu____786 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____798 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions  in
                     (match xs with
                      | x::[] -> x
                      | uu____804 -> mk_lex_list xs)
                  in
               let previous_dec = decreases_clause actuals expected_c  in
               let guard_one_letrec uu____816 =
                 match uu____816 with
                 | (l,t) ->
                     let uu____825 =
                       let uu____826 = FStar_Syntax_Subst.compress t  in
                       uu____826.FStar_Syntax_Syntax.n  in
                     (match uu____825 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____859  ->
                                    match uu____859 with
                                    | (x,imp) ->
                                        let uu____866 =
                                          FStar_Syntax_Syntax.is_null_bv x
                                           in
                                        if uu____866
                                        then
                                          let uu____869 =
                                            let uu____870 =
                                              let uu____872 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x
                                                 in
                                              Some uu____872  in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____870
                                              x.FStar_Syntax_Syntax.sort
                                             in
                                          (uu____869, imp)
                                        else (x, imp)))
                             in
                          let uu____874 =
                            FStar_Syntax_Subst.open_comp formals1 c  in
                          (match uu____874 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1  in
                               let precedes1 =
                                 let uu____887 =
                                   let uu____888 =
                                     let uu____889 =
                                       FStar_Syntax_Syntax.as_arg dec  in
                                     let uu____890 =
                                       let uu____892 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec
                                          in
                                       [uu____892]  in
                                     uu____889 :: uu____890  in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____888
                                    in
                                 uu____887 None r  in
                               let uu____897 = FStar_Util.prefix formals2  in
                               (match uu____897 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___93_923 = last1  in
                                      let uu____924 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___93_923.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___93_923.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____924
                                      }  in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)]  in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1
                                       in
                                    ((let uu____941 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low
                                         in
                                      if uu____941
                                      then
                                        let uu____942 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l
                                           in
                                        let uu____943 =
                                          FStar_Syntax_Print.term_to_string t
                                           in
                                        let uu____944 =
                                          FStar_Syntax_Print.term_to_string
                                            t'
                                           in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____942 uu____943 uu____944
                                      else ());
                                     (l, t'))))
                      | uu____948 ->
                          raise
                            (FStar_Errors.Error
                               ("Annotated type of 'let rec' must be an arrow",
                                 (t.FStar_Syntax_Syntax.pos))))
                  in
               FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))
  
let rec tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___94_1231 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___94_1231.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___94_1231.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___94_1231.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___94_1231.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___94_1231.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___94_1231.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___94_1231.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___94_1231.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___94_1231.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___94_1231.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___94_1231.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___94_1231.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___94_1231.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___94_1231.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___94_1231.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___94_1231.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___94_1231.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___94_1231.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___94_1231.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___94_1231.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___94_1231.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___94_1231.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___94_1231.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___94_1231.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___94_1231.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___94_1231.FStar_TypeChecker_Env.is_native_tactic)
         }) e

and tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      (let uu____1240 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____1240
       then
         let uu____1241 =
           let uu____1242 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1242  in
         let uu____1243 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____1241 uu____1243
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1249 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1267 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1272 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1281 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1282 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1283 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1284 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1285 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1295 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1303 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1308 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1314 = tc_tot_or_gtot_term env1 e1  in
           (match uu____1314 with
            | (e2,c,g) ->
                let g1 =
                  let uu___95_1325 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___95_1325.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___95_1325.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___95_1325.FStar_TypeChecker_Env.implicits)
                  }  in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1338 = FStar_Syntax_Util.type_u ()  in
           (match uu____1338 with
            | (t,u) ->
                let uu____1346 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____1346 with
                 | (e2,c,g) ->
                     let uu____1356 =
                       let uu____1365 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____1365 with
                       | (env2,uu____1378) -> tc_pats env2 pats  in
                     (match uu____1356 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___96_1399 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___96_1399.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___96_1399.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___96_1399.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____1400 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____1411 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____1400, c, uu____1411))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1419 =
             let uu____1420 = FStar_Syntax_Subst.compress e1  in
             uu____1420.FStar_Syntax_Syntax.n  in
           (match uu____1419 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1426,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1428;
                               FStar_Syntax_Syntax.lbtyp = uu____1429;
                               FStar_Syntax_Syntax.lbeff = uu____1430;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1448 =
                  let uu____1452 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit
                     in
                  tc_term uu____1452 e11  in
                (match uu____1448 with
                 | (e12,c1,g1) ->
                     let uu____1459 = tc_term env1 e2  in
                     (match uu____1459 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind
                              e12.FStar_Syntax_Syntax.pos env1 (Some e12) c1
                              (None, c2)
                             in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ
                             in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ
                             in
                          let e3 =
                            let uu____1476 =
                              let uu____1479 =
                                let uu____1480 =
                                  let uu____1488 =
                                    let uu____1492 =
                                      let uu____1494 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13)
                                         in
                                      [uu____1494]  in
                                    (false, uu____1492)  in
                                  (uu____1488, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____1480  in
                              FStar_Syntax_Syntax.mk uu____1479  in
                            uu____1476
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              e1.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          let e5 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e4,
                                    (FStar_Syntax_Syntax.Meta_desugared
                                       FStar_Syntax_Syntax.Sequence))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____1524 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e5, c, uu____1524)))
            | uu____1527 ->
                let uu____1528 = tc_term env1 e1  in
                (match uu____1528 with
                 | (e2,c,g) ->
                     let e3 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (e2,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Sequence))))
                         (Some
                            ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1552) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1567 = tc_term env1 e1  in
           (match uu____1567 with
            | (e2,c,g) ->
                let e3 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1593) ->
           let uu____1629 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____1629 with
            | (env0,uu____1637) ->
                let uu____1640 = tc_comp env0 expected_c  in
                (match uu____1640 with
                 | (expected_c1,uu____1648,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1
                        in
                     let uu____1653 =
                       let uu____1657 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____1657 e1  in
                     (match uu____1653 with
                      | (e2,c',g') ->
                          let uu____1664 =
                            let uu____1668 =
                              let uu____1671 = c'.FStar_Syntax_Syntax.comp ()
                                 in
                              (e2, uu____1671)  in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1668
                             in
                          (match uu____1664 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 (FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_ascribed
                                       (e3, ((FStar_Util.Inl t_res), None),
                                         (Some
                                            (FStar_Syntax_Util.comp_effect_name
                                               expected_c2)))))
                                   (Some (t_res.FStar_Syntax_Syntax.n))
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2
                                  in
                               let f =
                                 let uu____1722 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1722
                                  in
                               let topt1 = tc_tactic_opt env0 topt  in
                               let f1 =
                                 match topt1 with
                                 | None  -> f
                                 | Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic)
                                  in
                               let uu____1727 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____1727 with
                                | (e5,c,f2) ->
                                    let uu____1737 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2
                                       in
                                    (e5, c, uu____1737))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1741) ->
           let uu____1777 = FStar_Syntax_Util.type_u ()  in
           (match uu____1777 with
            | (k,u) ->
                let uu____1785 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____1785 with
                 | (t1,uu____1793,f) ->
                     let uu____1795 =
                       let uu____1799 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____1799 e1  in
                     (match uu____1795 with
                      | (e2,c,g) ->
                          let uu____1806 =
                            let uu____1809 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1812  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1809 e2 c f
                             in
                          (match uu____1806 with
                           | (c1,f1) ->
                               let uu____1818 =
                                 let uu____1822 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, ((FStar_Util.Inl t1), None),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env1 uu____1822 c1
                                  in
                               (match uu____1818 with
                                | (e3,c2,f2) ->
                                    let uu____1858 =
                                      let uu____1859 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1859
                                       in
                                    (e3, c2, uu____1858))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1860;
              FStar_Syntax_Syntax.pos = uu____1861;
              FStar_Syntax_Syntax.vars = uu____1862;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____1906 = FStar_Syntax_Util.head_and_args top  in
           (match uu____1906 with
            | (unary_op,uu____1920) ->
                let head1 =
                  let uu____1938 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1938
                   in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____1982);
              FStar_Syntax_Syntax.tk = uu____1983;
              FStar_Syntax_Syntax.pos = uu____1984;
              FStar_Syntax_Syntax.vars = uu____1985;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____2029 = FStar_Syntax_Util.head_and_args top  in
           (match uu____2029 with
            | (unary_op,uu____2043) ->
                let head1 =
                  let uu____2061 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (fst a).FStar_Syntax_Syntax.pos
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____2061
                   in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____2105;
              FStar_Syntax_Syntax.pos = uu____2106;
              FStar_Syntax_Syntax.vars = uu____2107;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2133 =
               let uu____2137 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               match uu____2137 with | (env0,uu____2145) -> tc_term env0 e1
                in
             match uu____2133 with
             | (e2,c,g) ->
                 let uu____2154 = FStar_Syntax_Util.head_and_args top  in
                 (match uu____2154 with
                  | (reify_op,uu____2168) ->
                      let u_c =
                        let uu____2184 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ  in
                        match uu____2184 with
                        | (uu____2188,c',uu____2190) ->
                            let uu____2191 =
                              let uu____2192 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ
                                 in
                              uu____2192.FStar_Syntax_Syntax.n  in
                            (match uu____2191 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2196 ->
                                 let uu____2197 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____2197 with
                                  | (t,u) ->
                                      let g_opt =
                                        FStar_TypeChecker_Rel.try_teq true
                                          env1 c'.FStar_Syntax_Syntax.res_typ
                                          t
                                         in
                                      ((match g_opt with
                                        | Some g' ->
                                            FStar_TypeChecker_Rel.force_trivial_guard
                                              env1 g'
                                        | None  ->
                                            let uu____2206 =
                                              let uu____2207 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c'
                                                 in
                                              let uu____2208 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ
                                                 in
                                              let uu____2209 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ
                                                 in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2207 uu____2208
                                                uu____2209
                                               in
                                            failwith uu____2206);
                                       u)))
                         in
                      let repr =
                        let uu____2211 = c.FStar_Syntax_Syntax.comp ()  in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2211 u_c
                         in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos
                         in
                      let c1 =
                        let uu____2233 = FStar_Syntax_Syntax.mk_Total repr
                           in
                        FStar_All.pipe_right uu____2233
                          FStar_Syntax_Util.lcomp_of_comp
                         in
                      let uu____2234 = comp_check_expected_typ env1 e3 c1  in
                      (match uu____2234 with
                       | (e4,c2,g') ->
                           let uu____2244 =
                             FStar_TypeChecker_Rel.conj_guard g g'  in
                           (e4, c2, uu____2244)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2246;
              FStar_Syntax_Syntax.pos = uu____2247;
              FStar_Syntax_Syntax.vars = uu____2248;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2280 =
               let uu____2281 =
                 let uu____2282 =
                   let uu____2285 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str
                      in
                   (uu____2285, (e1.FStar_Syntax_Syntax.pos))  in
                 FStar_Errors.Error uu____2282  in
               raise uu____2281  in
             let uu____2289 = FStar_Syntax_Util.head_and_args top  in
             match uu____2289 with
             | (reflect_op,uu____2303) ->
                 let uu____2318 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____2318 with
                  | None  -> no_reflect ()
                  | Some (ed,qualifiers) ->
                      let uu____2336 =
                        let uu____2337 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____2337  in
                      if uu____2336
                      then no_reflect ()
                      else
                        (let uu____2343 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____2343 with
                         | (env_no_ex,topt) ->
                             let uu____2354 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____2369 =
                                   let uu____2372 =
                                     let uu____2373 =
                                       let uu____2383 =
                                         let uu____2385 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____2386 =
                                           let uu____2388 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____2388]  in
                                         uu____2385 :: uu____2386  in
                                       (repr, uu____2383)  in
                                     FStar_Syntax_Syntax.Tm_app uu____2373
                                      in
                                   FStar_Syntax_Syntax.mk uu____2372  in
                                 uu____2369 None top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____2398 =
                                 let uu____2402 =
                                   let uu____2403 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____2403
                                     FStar_Pervasives.fst
                                    in
                                 tc_tot_or_gtot_term uu____2402 t  in
                               match uu____2398 with
                               | (t1,uu____2420,g) ->
                                   let uu____2422 =
                                     let uu____2423 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____2423.FStar_Syntax_Syntax.n  in
                                   (match uu____2422 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2434,(res,uu____2436)::
                                         (wp,uu____2438)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2472 -> failwith "Impossible")
                                in
                             (match uu____2354 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2496 =
                                    let uu____2499 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____2499 with
                                    | (e2,c,g) ->
                                        ((let uu____2509 =
                                            let uu____2510 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2510
                                             in
                                          if uu____2509
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2516 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____2516 with
                                          | None  ->
                                              ((let uu____2521 =
                                                  let uu____2525 =
                                                    let uu____2528 =
                                                      let uu____2529 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____2530 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2529 uu____2530
                                                       in
                                                    (uu____2528,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____2525]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2521);
                                               (let uu____2535 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____2535)))
                                          | Some g' ->
                                              let uu____2537 =
                                                let uu____2538 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2538
                                                 in
                                              (e2, uu____2537)))
                                     in
                                  (match uu____2496 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2545 =
                                           let uu____2546 =
                                             let uu____2547 =
                                               let uu____2548 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____2548]  in
                                             let uu____2549 =
                                               let uu____2555 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____2555]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2547;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2549;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2546
                                            in
                                         FStar_All.pipe_right uu____2545
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e2, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____2576 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____2576 with
                                        | (e4,c1,g') ->
                                            let uu____2586 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____2586))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,(tau,uu____2589)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           (match env1.FStar_TypeChecker_Env.expected_typ with
            | Some typ -> tc_synth env1 typ tau
            | None  ->
                let uu____2615 =
                  let uu____2616 =
                    let uu____2619 = FStar_TypeChecker_Env.get_range env1  in
                    ("synth_by_tactic: need a type annotation when no expected type is present",
                      uu____2619)
                     in
                  FStar_Errors.Error uu____2616  in
                raise uu____2615)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(a,uu____2625)::(tau,uu____2627)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 -> tc_synth env1 a tau
       | FStar_Syntax_Syntax.Tm_app
           (head1,(a,uu____2659)::uu____2660::(tau,uu____2662)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 -> tc_synth env1 a tau
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____2718 =
               let uu____2719 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____2719 FStar_Pervasives.fst  in
             FStar_All.pipe_right uu____2718 instantiate_both  in
           ((let uu____2728 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____2728
             then
               let uu____2729 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____2730 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2729
                 uu____2730
             else ());
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.quote_lid
                   -> true
               | uu____2734 -> false  in
             let uu____2735 = tc_term (no_inst env2) head1  in
             match uu____2735 with
             | (head2,chead,g_head) ->
                 let uu____2745 =
                   let uu____2749 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____2749
                   then
                     let uu____2753 =
                       let uu____2757 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____2757
                        in
                     match uu____2753 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____2766 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____2767 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c
                                    in
                                 Prims.op_Negation uu____2767))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                              in
                           if uu____2766
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c  in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2  in
                      let uu____2772 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env3 head2 chead g_head args
                        uu____2772)
                    in
                 (match uu____2745 with
                  | (e1,c,g) ->
                      ((let uu____2781 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____2781
                        then
                          let uu____2782 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2782
                        else ());
                       (let uu____2784 = comp_check_expected_typ env0 e1 c
                           in
                        match uu____2784 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____2795 =
                                let uu____2796 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____2796.FStar_Syntax_Syntax.n  in
                              match uu____2795 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2800) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___97_2832 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___97_2832.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___97_2832.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___97_2832.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2857 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____2859 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____2859
                               in
                            ((let uu____2861 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____2861
                              then
                                let uu____2862 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____2863 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2862 uu____2863
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2893 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____2893 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____2905 = tc_term env12 e1  in
                (match uu____2905 with
                 | (e11,c1,g1) ->
                     let uu____2915 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2921 = FStar_Syntax_Util.type_u ()  in
                           (match uu____2921 with
                            | (k,uu____2927) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k  in
                                let uu____2929 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t
                                   in
                                (uu____2929, res_t))
                        in
                     (match uu____2915 with
                      | (env_branches,res_t) ->
                          ((let uu____2936 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____2936
                            then
                              let uu____2937 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2937
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____2988 =
                              let uu____2991 =
                                FStar_List.fold_right
                                  (fun uu____3010  ->
                                     fun uu____3011  ->
                                       match (uu____3010, uu____3011) with
                                       | ((uu____3043,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____3076 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), uu____3076))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____2991 with
                              | (cases,g) ->
                                  let uu____3097 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____3097, g)
                               in
                            match uu____2988 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (Some e11) c1
                                    ((Some guard_x), c_branches)
                                   in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____3150  ->
                                              match uu____3150 with
                                              | ((pat,wopt,br),uu____3166,lc,uu____3168)
                                                  ->
                                                  let uu____3175 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  (pat, wopt, uu____3175)))
                                       in
                                    let e2 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_match
                                            (scrutinee, branches)))
                                        (Some
                                           ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let e3 =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env1 e2
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    (FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_ascribed
                                          (e3,
                                            ((FStar_Util.Inl
                                                (cres.FStar_Syntax_Syntax.res_typ)),
                                              None),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.eff_name)))))
                                      None e3.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____3231 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____3231
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____3238 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____3238  in
                                     let lb =
                                       let uu____3242 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (FStar_Util.Inl guard_x);
                                         FStar_Syntax_Syntax.lbunivs = [];
                                         FStar_Syntax_Syntax.lbtyp =
                                           (c1.FStar_Syntax_Syntax.res_typ);
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____3242;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       }  in
                                     let e2 =
                                       let uu____3246 =
                                         let uu____3249 =
                                           let uu____3250 =
                                             let uu____3258 =
                                               let uu____3259 =
                                                 let uu____3260 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____3260]  in
                                               FStar_Syntax_Subst.close
                                                 uu____3259 e_match
                                                in
                                             ((false, [lb]), uu____3258)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____3250
                                            in
                                         FStar_Syntax_Syntax.mk uu____3249
                                          in
                                       uu____3246
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____3274 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____3274
                                  then
                                    let uu____3275 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____3276 =
                                      let uu____3277 =
                                        cres.FStar_Syntax_Syntax.comp ()  in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____3277
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____3275 uu____3276
                                  else ());
                                 (let uu____3279 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e2, cres, uu____3279))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3282;
                FStar_Syntax_Syntax.lbunivs = uu____3283;
                FStar_Syntax_Syntax.lbtyp = uu____3284;
                FStar_Syntax_Syntax.lbeff = uu____3285;
                FStar_Syntax_Syntax.lbdef = uu____3286;_}::[]),uu____3287)
           ->
           ((let uu____3302 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____3302
             then
               let uu____3303 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____3303
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____3305),uu____3306) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3316;
                FStar_Syntax_Syntax.lbunivs = uu____3317;
                FStar_Syntax_Syntax.lbtyp = uu____3318;
                FStar_Syntax_Syntax.lbeff = uu____3319;
                FStar_Syntax_Syntax.lbdef = uu____3320;_}::uu____3321),uu____3322)
           ->
           ((let uu____3338 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____3338
             then
               let uu____3339 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____3339
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3341),uu____3342) ->
           check_inner_let_rec env1 top)

and tc_synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let uu____3357 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____3357 with
        | (env',uu____3365) ->
            let uu____3368 = tc_term env' typ  in
            (match uu____3368 with
             | (typ1,uu____3376,g1) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                  (let uu____3379 = tc_term env' tau  in
                   match uu____3379 with
                   | (tau1,c,g2) ->
                       (FStar_TypeChecker_Rel.force_trivial_guard env' g2;
                        (let uu____3391 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "Tac")
                            in
                         if uu____3391
                         then
                           let uu____3392 =
                             FStar_Syntax_Print.term_to_string tau1  in
                           let uu____3393 =
                             FStar_Syntax_Print.term_to_string typ1  in
                           FStar_Util.print2
                             "Running tactic %s at return type %s\n"
                             uu____3392 uu____3393
                         else ());
                        (let t =
                           env.FStar_TypeChecker_Env.synth env' typ1 tau1  in
                         (let uu____3397 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Tac")
                             in
                          if uu____3397
                          then
                            let uu____3398 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print1 "Got %s\n" uu____3398
                          else ());
                         FStar_TypeChecker_Util.check_uvars
                           tau1.FStar_Syntax_Syntax.pos t;
                         tc_term env t)))))

and tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option -> FStar_Syntax_Syntax.term option
  =
  fun env  ->
    fun topt  ->
      match topt with
      | None  -> None
      | Some tactic ->
          let uu____3414 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit
             in
          (match uu____3414 with
           | (tactic1,uu____3420,uu____3421) -> Some tactic1)

and tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____3456 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____3456 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3469 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____3469
              then FStar_Util.Inl t1
              else
                (let uu____3473 =
                   let uu____3474 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3474
                    in
                 FStar_Util.Inr uu____3473)
               in
            let is_data_ctor uu___86_3483 =
              match uu___86_3483 with
              | Some (FStar_Syntax_Syntax.Data_ctor ) -> true
              | Some (FStar_Syntax_Syntax.Record_ctor uu____3485) -> true
              | uu____3489 -> false  in
            let uu____3491 =
              (is_data_ctor dc) &&
                (let uu____3492 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____3492)
               in
            if uu____3491
            then
              let uu____3498 =
                let uu____3499 =
                  let uu____3502 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  let uu____3505 = FStar_TypeChecker_Env.get_range env1  in
                  (uu____3502, uu____3505)  in
                FStar_Errors.Error uu____3499  in
              raise uu____3498
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3516 =
            let uu____3517 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3517
             in
          failwith uu____3516
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3536 =
              let uu____3537 = FStar_Syntax_Subst.compress t1  in
              uu____3537.FStar_Syntax_Syntax.n  in
            match uu____3536 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3540 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3548 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___98_3568 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___98_3568.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___98_3568.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___98_3568.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____3596 =
            let uu____3603 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____3603 with
            | None  ->
                let uu____3611 = FStar_Syntax_Util.type_u ()  in
                (match uu____3611 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard)  in
          (match uu____3596 with
           | (t,uu____3632,g0) ->
               let uu____3640 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____3640 with
                | (e1,uu____3651,g1) ->
                    let uu____3659 =
                      let uu____3660 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____3660
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____3661 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____3659, uu____3661)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3663 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3672 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____3672)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____3663 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___99_3686 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___99_3686.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___99_3686.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____3689 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____3689 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3702 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____3702
                       then FStar_Util.Inl t1
                       else
                         (let uu____3706 =
                            let uu____3707 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3707
                             in
                          FStar_Util.Inr uu____3706)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3713;
             FStar_Syntax_Syntax.pos = uu____3714;
             FStar_Syntax_Syntax.vars = uu____3715;_},uu____3716)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.synth_lid
          ->
          let uu____3721 =
            let uu____3722 =
              let uu____3725 = FStar_TypeChecker_Env.get_range env1  in
              ("Badly instantiated synth_by_tactic", uu____3725)  in
            FStar_Errors.Error uu____3722  in
          raise uu____3721
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.synth_lid ->
          let uu____3730 =
            let uu____3731 =
              let uu____3734 = FStar_TypeChecker_Env.get_range env1  in
              ("Badly instantiated synth_by_tactic", uu____3734)  in
            FStar_Errors.Error uu____3731  in
          raise uu____3730
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3739;
             FStar_Syntax_Syntax.pos = uu____3740;
             FStar_Syntax_Syntax.vars = uu____3741;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____3749 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3749 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3775 =
                     let uu____3776 =
                       let uu____3779 =
                         let uu____3780 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____3781 =
                           FStar_Util.string_of_int (FStar_List.length us1)
                            in
                         let uu____3788 =
                           FStar_Util.string_of_int (FStar_List.length us')
                            in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____3780 uu____3781 uu____3788
                          in
                       let uu____3795 = FStar_TypeChecker_Env.get_range env1
                          in
                       (uu____3779, uu____3795)  in
                     FStar_Errors.Error uu____3776  in
                   raise uu____3775)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____3802 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___100_3804 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___101_3805 = fv.FStar_Syntax_Syntax.fv_name
                           in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___101_3805.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___101_3805.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___100_3804.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___100_3804.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range  in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3821 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3821 us1  in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3833 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3833 with
           | ((us,t),range) ->
               ((let uu____3851 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____3851
                 then
                   let uu____3852 =
                     let uu____3853 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____3853  in
                   let uu____3854 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3855 = FStar_Range.string_of_range range  in
                   let uu____3856 = FStar_Range.string_of_use_range range  in
                   let uu____3857 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
                     uu____3852 uu____3854 uu____3855 uu____3856 uu____3857
                 else ());
                (let fv' =
                   let uu___102_3860 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___103_3861 = fv.FStar_Syntax_Syntax.fv_name
                           in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___103_3861.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___103_3861.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___102_3860.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___102_3860.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range  in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3877 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3877 us  in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
              (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____3913 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3913 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____3922 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____3922 with
                | (env2,uu____3930) ->
                    let uu____3933 = tc_binders env2 bs1  in
                    (match uu____3933 with
                     | (bs2,env3,g,us) ->
                         let uu____3945 = tc_comp env3 c1  in
                         (match uu____3945 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___104_3958 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___104_3958.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___104_3958.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___104_3958.FStar_Syntax_Syntax.vars)
                                }  in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us)
                                   in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos
                                   in
                                let g1 =
                                  let uu____3979 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3979
                                   in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u  in
          let t =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1)))
              None top.FStar_Syntax_Syntax.pos
             in
          let e1 =
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1))
              (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____4014 =
            let uu____4017 =
              let uu____4018 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____4018]  in
            FStar_Syntax_Subst.open_term uu____4017 phi  in
          (match uu____4014 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____4025 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____4025 with
                | (env2,uu____4033) ->
                    let uu____4036 =
                      let uu____4043 = FStar_List.hd x1  in
                      tc_binder env2 uu____4043  in
                    (match uu____4036 with
                     | (x2,env3,f1,u) ->
                         ((let uu____4060 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____4060
                           then
                             let uu____4061 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____4062 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____4063 =
                               FStar_Syntax_Print.bv_to_string (fst x2)  in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____4061 uu____4062 uu____4063
                           else ());
                          (let uu____4065 = FStar_Syntax_Util.type_u ()  in
                           match uu____4065 with
                           | (t_phi,uu____4072) ->
                               let uu____4073 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____4073 with
                                | (phi2,uu____4081,f2) ->
                                    let e1 =
                                      let uu___105_4086 =
                                        FStar_Syntax_Util.refine (fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___105_4086.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___105_4086.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___105_4086.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____4105 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____4105
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____4114) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____4129 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____4129
            then
              let uu____4130 =
                FStar_Syntax_Print.term_to_string
                  (let uu___106_4131 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___106_4131.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___106_4131.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___106_4131.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____4130
            else ());
           (let uu____4140 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____4140 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____4148 ->
          let uu____4149 =
            let uu____4150 = FStar_Syntax_Print.term_to_string top  in
            let uu____4151 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____4150
              uu____4151
             in
          failwith uu____4149

and tc_constant :
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____4157 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____4158,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____4164,Some uu____4165) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____4173 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____4177 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____4178 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____4179 ->
          FStar_TypeChecker_Common.t_range
      | uu____4180 -> raise (FStar_Errors.Error ("Unsupported constant", r))

and tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun c  ->
      let c0 = c  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____4191) ->
          let uu____4198 = FStar_Syntax_Util.type_u ()  in
          (match uu____4198 with
           | (k,u) ->
               let uu____4206 = tc_check_tot_or_gtot_term env t k  in
               (match uu____4206 with
                | (t1,uu____4214,g) ->
                    let uu____4216 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u)  in
                    (uu____4216, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____4218) ->
          let uu____4225 = FStar_Syntax_Util.type_u ()  in
          (match uu____4225 with
           | (k,u) ->
               let uu____4233 = tc_check_tot_or_gtot_term env t k  in
               (match uu____4233 with
                | (t1,uu____4241,g) ->
                    let uu____4243 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u)  in
                    (uu____4243, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant None
             in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_uinst (head1, us))) None
                  c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____4259 =
              let uu____4260 =
                let uu____4261 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____4261 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____4260  in
            uu____4259 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____4266 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____4266 with
           | (tc1,uu____4274,f) ->
               let uu____4276 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____4276 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4306 =
                        let uu____4307 = FStar_Syntax_Subst.compress head3
                           in
                        uu____4307.FStar_Syntax_Syntax.n  in
                      match uu____4306 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4310,us) -> us
                      | uu____4316 -> []  in
                    let uu____4317 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____4317 with
                     | (uu____4330,args1) ->
                         let uu____4346 =
                           let uu____4358 = FStar_List.hd args1  in
                           let uu____4367 = FStar_List.tl args1  in
                           (uu____4358, uu____4367)  in
                         (match uu____4346 with
                          | (res,args2) ->
                              let uu____4409 =
                                let uu____4414 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___87_4424  ->
                                          match uu___87_4424 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4430 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____4430 with
                                               | (env1,uu____4437) ->
                                                   let uu____4440 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____4440 with
                                                    | (e1,uu____4447,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____4414
                                  FStar_List.unzip
                                 in
                              (match uu____4409 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___107_4470 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___107_4470.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___107_4470.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____4474 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____4474 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____4477 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____4477))))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4485 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4486 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4490 = aux u3  in FStar_Syntax_Syntax.U_succ uu____4490
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4493 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____4493
        | FStar_Syntax_Syntax.U_name x -> u2  in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4497 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____4497 FStar_Pervasives.snd
         | uu____4502 -> aux u)

and tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail msg t =
            let uu____4523 =
              let uu____4524 =
                let uu____4527 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top
                   in
                (uu____4527, (top.FStar_Syntax_Syntax.pos))  in
              FStar_Errors.Error uu____4524  in
            raise uu____4523  in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4581 bs2 bs_expected1 =
              match uu____4581 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit
                            uu____4672)) ->
                             let uu____4675 =
                               let uu____4676 =
                                 let uu____4679 =
                                   let uu____4680 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4680
                                    in
                                 let uu____4681 =
                                   FStar_Syntax_Syntax.range_of_bv hd1  in
                                 (uu____4679, uu____4681)  in
                               FStar_Errors.Error uu____4676  in
                             raise uu____4675
                         | (Some (FStar_Syntax_Syntax.Implicit
                            uu____4682),None ) ->
                             let uu____4685 =
                               let uu____4686 =
                                 let uu____4689 =
                                   let uu____4690 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4690
                                    in
                                 let uu____4691 =
                                   FStar_Syntax_Syntax.range_of_bv hd1  in
                                 (uu____4689, uu____4691)  in
                               FStar_Errors.Error uu____4686  in
                             raise uu____4685
                         | uu____4692 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____4696 =
                           let uu____4699 =
                             let uu____4700 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____4700.FStar_Syntax_Syntax.n  in
                           match uu____4699 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4705 ->
                               ((let uu____4707 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____4707
                                 then
                                   let uu____4708 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4708
                                 else ());
                                (let uu____4710 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____4710 with
                                 | (t,uu____4717,g1) ->
                                     let g2 =
                                       let uu____4720 =
                                         FStar_TypeChecker_Env.get_range env2
                                          in
                                       let uu____4721 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t
                                          in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4720
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4721
                                        in
                                     let g3 =
                                       let uu____4723 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4723
                                        in
                                     (t, g3)))
                            in
                         match uu____4696 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___108_4739 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___108_4739.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___108_4739.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____4748 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____4748
                                in
                             aux (env3, (b :: out), g1, subst2) bs3
                               bs_expected2))
                   | (rest,[]) ->
                       (env2, (FStar_List.rev out),
                         (Some (FStar_Util.Inl rest)), g, subst1)
                   | ([],rest) ->
                       (env2, (FStar_List.rev out),
                         (Some (FStar_Util.Inr rest)), g, subst1))
               in
            aux (env1, [], FStar_TypeChecker_Rel.trivial_guard, []) bs1
              bs_expected
             in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____4850 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4854 = tc_binders env1 bs  in
                  match uu____4854 with
                  | (bs1,envbody,g,uu____4875) ->
                      let uu____4876 =
                        let uu____4883 =
                          let uu____4884 = FStar_Syntax_Subst.compress body1
                             in
                          uu____4884.FStar_Syntax_Syntax.n  in
                        match uu____4883 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4896) ->
                            let uu____4932 = tc_comp envbody c  in
                            (match uu____4932 with
                             | (c1,uu____4943,g') ->
                                 let uu____4945 =
                                   tc_tactic_opt envbody tacopt  in
                                 let uu____4947 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((Some c1), uu____4945, body1, uu____4947))
                        | uu____4950 -> (None, None, body1, g)  in
                      (match uu____4876 with
                       | (copt,tacopt,body2,g1) ->
                           (None, bs1, [], copt, tacopt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____5009 =
                    let uu____5010 = FStar_Syntax_Subst.compress t2  in
                    uu____5010.FStar_Syntax_Syntax.n  in
                  match uu____5009 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____5027 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____5039 -> failwith "Impossible");
                       (let uu____5043 = tc_binders env1 bs  in
                        match uu____5043 with
                        | (bs1,envbody,g,uu____5065) ->
                            let uu____5066 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____5066 with
                             | (envbody1,uu____5085) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____5096;
                         FStar_Syntax_Syntax.tk = uu____5097;
                         FStar_Syntax_Syntax.pos = uu____5098;
                         FStar_Syntax_Syntax.vars = uu____5099;_},uu____5100)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____5126 -> failwith "Impossible");
                       (let uu____5130 = tc_binders env1 bs  in
                        match uu____5130 with
                        | (bs1,envbody,g,uu____5152) ->
                            let uu____5153 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____5153 with
                             | (envbody1,uu____5172) ->
                                 ((Some (t2, true)), bs1, [], None, None,
                                   envbody1, body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____5184) ->
                      let uu____5189 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____5189 with
                       | (uu____5218,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, tacopt, env2,
                             body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____5258 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____5258 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5321 c_expected2 =
                               match uu____5321 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____5382 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____5382)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____5399 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5399
                                           in
                                        let uu____5400 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____5400)
                                    | Some (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        if FStar_Syntax_Util.is_named_tot c
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env3
                                              (FStar_Syntax_Util.comp_result
                                                 c)
                                             in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____5441 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____5441 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5453 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____5453 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5480 =
                                                           let uu____5496 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____5496,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____5480
                                                           c_expected4))
                                           | uu____5505 ->
                                               let uu____5506 =
                                                 let uu____5507 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3
                                                    in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____5507
                                                  in
                                               fail uu____5506 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2)
                                in
                             let uu____5523 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____5523 c_expected1  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___109_5561 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___109_5561.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___109_5561.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___109_5561.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___109_5561.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___109_5561.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___109_5561.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___109_5561.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___109_5561.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___109_5561.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___109_5561.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___109_5561.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___109_5561.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___109_5561.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___109_5561.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___109_5561.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___109_5561.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___109_5561.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___109_5561.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___109_5561.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___109_5561.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___109_5561.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___109_5561.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___109_5561.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___109_5561.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___109_5561.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___109_5561.FStar_TypeChecker_Env.is_native_tactic)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5575  ->
                                     fun uu____5576  ->
                                       match (uu____5575, uu____5576) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5601 =
                                             let uu____5605 =
                                               let uu____5606 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____5606
                                                 FStar_Pervasives.fst
                                                in
                                             tc_term uu____5605 t3  in
                                           (match uu____5601 with
                                            | (t4,uu____5618,uu____5619) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5626 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___110_5627
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___110_5627.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___110_5627.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____5626 ::
                                                        letrec_binders
                                                  | uu____5628 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____5631 =
                             check_actuals_against_formals env1 bs
                               bs_expected1
                              in
                           (match uu____5631 with
                            | (envbody,bs1,g,c) ->
                                let uu____5663 =
                                  let uu____5667 =
                                    FStar_TypeChecker_Env.should_verify env1
                                     in
                                  if uu____5667
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, [])  in
                                (match uu____5663 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), None, envbody2, body1, g))))
                  | uu____5703 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5718 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____5718
                      else
                        (let uu____5720 =
                           expected_function_typ1 env1 None body1  in
                         match uu____5720 with
                         | (uu____5748,bs1,uu____5750,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, tacopt,
                               envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____5775 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____5775 with
          | (env1,topt) ->
              ((let uu____5787 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____5787
                then
                  let uu____5788 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5788
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5792 = expected_function_typ1 env1 topt body  in
                match uu____5792 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5827 =
                      tc_term
                        (let uu___111_5831 = envbody  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___111_5831.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___111_5831.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___111_5831.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___111_5831.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___111_5831.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___111_5831.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___111_5831.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___111_5831.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___111_5831.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___111_5831.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___111_5831.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___111_5831.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___111_5831.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___111_5831.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___111_5831.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___111_5831.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___111_5831.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___111_5831.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___111_5831.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___111_5831.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___111_5831.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___111_5831.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___111_5831.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___111_5831.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___111_5831.FStar_TypeChecker_Env.is_native_tactic)
                         }) body1
                       in
                    (match uu____5827 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         ((let uu____5840 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits")
                              in
                           if uu____5840
                           then
                             let uu____5841 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits)
                                in
                             let uu____5852 =
                               let uu____5853 =
                                 cbody.FStar_Syntax_Syntax.comp ()  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5853
                                in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5841 uu____5852
                           else ());
                          (let uu____5855 =
                             let uu____5859 =
                               let uu____5862 =
                                 cbody.FStar_Syntax_Syntax.comp ()  in
                               (body2, uu____5862)  in
                             check_expected_effect
                               (let uu___112_5867 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___112_5867.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___112_5867.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___112_5867.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___112_5867.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___112_5867.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___112_5867.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___112_5867.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___112_5867.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___112_5867.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___112_5867.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___112_5867.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___112_5867.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___112_5867.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___112_5867.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___112_5867.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___112_5867.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___112_5867.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___112_5867.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___112_5867.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___112_5867.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___112_5867.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___112_5867.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___112_5867.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___112_5867.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___112_5867.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___112_5867.FStar_TypeChecker_Env.is_native_tactic)
                                }) c_opt uu____5859
                              in
                           match uu____5855 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard
                                  in
                               let guard2 =
                                 let uu____5876 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5877 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1
                                         in
                                      Prims.op_Negation uu____5877)
                                    in
                                 if uu____5876
                                 then
                                   let uu____5878 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1
                                      in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5878
                                 else
                                   (let guard2 =
                                      let uu____5881 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1
                                         in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5881
                                       in
                                    guard2)
                                  in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1  in
                               let e =
                                 FStar_Syntax_Util.abs bs1 body3
                                   (Some
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         (FStar_Util.dflt cbody1 c_opt)))
                                  in
                               let uu____5888 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t
                                        in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5903 -> (e, t1, guard2)
                                      | uu____5911 ->
                                          let uu____5912 =
                                            if use_teq
                                            then
                                              let uu____5917 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed
                                                 in
                                              (e, uu____5917)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1
                                             in
                                          (match uu____5912 with
                                           | (e1,guard') ->
                                               let uu____5924 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard'
                                                  in
                                               (e1, t1, uu____5924)))
                                 | None  -> (e, tfun_computed, guard2)  in
                               (match uu____5888 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1
                                       in
                                    let uu____5937 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3
                                       in
                                    (match uu____5937 with
                                     | (c1,g1) -> (e1, c1, g1))))))))

and check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)
            Prims.list ->
            FStar_Syntax_Syntax.typ option ->
              ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.lcomp *
                FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = chead.FStar_Syntax_Syntax.res_typ  in
              (let uu____5974 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____5974
               then
                 let uu____5975 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____5976 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5975
                   uu____5976
               else ());
              (let monadic_application uu____6014 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____6014 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres1 =
                       let uu___113_6051 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___113_6051.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___113_6051.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___113_6051.FStar_Syntax_Syntax.comp)
                       }  in
                     let uu____6052 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1
                              in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard
                              in
                           (cres2, g)
                       | uu____6061 ->
                           let g =
                             let uu____6066 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard
                                in
                             FStar_All.pipe_right uu____6066
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____6067 =
                             let uu____6068 =
                               let uu____6071 =
                                 let uu____6072 =
                                   let uu____6073 =
                                     cres1.FStar_Syntax_Syntax.comp ()  in
                                   FStar_Syntax_Util.arrow bs uu____6073  in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____6072
                                  in
                               FStar_Syntax_Syntax.mk_Total uu____6071  in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____6068
                              in
                           (uu____6067, g)
                        in
                     (match uu____6052 with
                      | (cres2,guard1) ->
                          ((let uu____6084 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____6084
                            then
                              let uu____6085 =
                                FStar_Syntax_Print.lcomp_to_string cres2  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____6085
                            else ());
                           (let cres3 =
                              let uu____6088 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2
                                 in
                              if uu____6088
                              then
                                let term =
                                  (FStar_Syntax_Syntax.mk_Tm_app head2
                                     (FStar_List.rev arg_rets_rev)) None
                                    head2.FStar_Syntax_Syntax.pos
                                   in
                                FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                  env term cres2
                              else cres2  in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____6111  ->
                                     match uu____6111 with
                                     | ((e,q),x,c) ->
                                         let uu____6134 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____6134
                                         then
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             (Some e) c (x, out_c)
                                         else
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             None c (x, out_c)) cres3
                                arg_comps_rev
                               in
                            let comp1 =
                              FStar_TypeChecker_Util.bind
                                head2.FStar_Syntax_Syntax.pos env None chead1
                                (None, comp)
                               in
                            let shortcuts_evaluation_order =
                              let uu____6143 =
                                let uu____6144 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____6144.FStar_Syntax_Syntax.n  in
                              match uu____6143 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____6148 -> false  in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____6158  ->
                                         match uu____6158 with
                                         | (arg,uu____6166,uu____6167) -> arg
                                             :: args1) [] arg_comps_rev
                                   in
                                let app =
                                  (FStar_Syntax_Syntax.mk_Tm_app head2 args1)
                                    (Some
                                       ((comp1.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                    r
                                   in
                                let app1 =
                                  FStar_TypeChecker_Util.maybe_lift env app
                                    cres3.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_TypeChecker_Util.maybe_monadic env app1
                                  comp1.FStar_Syntax_Syntax.eff_name
                                  comp1.FStar_Syntax_Syntax.res_typ
                              else
                                (let uu____6179 =
                                   let map_fun uu____6214 =
                                     match uu____6214 with
                                     | ((e,q),uu____6234,c) ->
                                         let uu____6240 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____6240
                                         then (None, (e, q))
                                         else
                                           (let x =
                                              FStar_Syntax_Syntax.new_bv None
                                                c.FStar_Syntax_Syntax.res_typ
                                               in
                                            let e1 =
                                              FStar_TypeChecker_Util.maybe_lift
                                                env e
                                                c.FStar_Syntax_Syntax.eff_name
                                                comp1.FStar_Syntax_Syntax.eff_name
                                                c.FStar_Syntax_Syntax.res_typ
                                               in
                                            let uu____6270 =
                                              let uu____6273 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              (uu____6273, q)  in
                                            ((Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____6270))
                                      in
                                   let uu____6291 =
                                     let uu____6305 =
                                       let uu____6318 =
                                         let uu____6326 =
                                           let uu____6331 =
                                             FStar_Syntax_Syntax.as_arg head2
                                              in
                                           (uu____6331, None, chead1)  in
                                         uu____6326 :: arg_comps_rev  in
                                       FStar_List.map map_fun uu____6318  in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6305
                                      in
                                   match uu____6291 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6426 =
                                         let uu____6427 =
                                           FStar_List.hd reverse_args  in
                                         fst uu____6427  in
                                       let uu____6432 =
                                         let uu____6436 =
                                           FStar_List.tl reverse_args  in
                                         FStar_List.rev uu____6436  in
                                       (lifted_args, uu____6426, uu____6432)
                                    in
                                 match uu____6179 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       (FStar_Syntax_Syntax.mk_Tm_app head3
                                          args1)
                                         (Some
                                            ((comp1.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         r
                                        in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ
                                        in
                                     let app2 =
                                       FStar_TypeChecker_Util.maybe_monadic
                                         env app1
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ
                                        in
                                     let bind_lifted_args e uu___88_6504 =
                                       match uu___88_6504 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1
                                              in
                                           let letbinding =
                                             let uu____6546 =
                                               let uu____6549 =
                                                 let uu____6550 =
                                                   let uu____6558 =
                                                     let uu____6559 =
                                                       let uu____6560 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____6560]  in
                                                     FStar_Syntax_Subst.close
                                                       uu____6559 e
                                                      in
                                                   ((false, [lb]),
                                                     uu____6558)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6550
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6549
                                                in
                                             uu____6546 None
                                               e.FStar_Syntax_Syntax.pos
                                              in
                                           (FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (letbinding,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      (m,
                                                        (comp1.FStar_Syntax_Syntax.res_typ))))))
                                             None e.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args)
                               in
                            let uu____6594 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1
                               in
                            match uu____6594 with
                            | (comp2,g) -> (app, comp2, g))))
                  in
               let rec tc_args head_info uu____6648 bs args1 =
                 match uu____6648 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6731))::rest,
                         (uu____6733,None )::uu____6734) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t1 = check_no_escape (Some head1) env fvs t  in
                          let uu____6771 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____6771 with
                           | (varg,uu____6782,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1
                                  in
                               let arg =
                                 let uu____6795 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____6795)  in
                               let uu____6796 =
                                 let uu____6814 =
                                   let uu____6822 =
                                     let uu____6829 =
                                       let uu____6830 =
                                         FStar_Syntax_Syntax.mk_Total t1  in
                                       FStar_All.pipe_right uu____6830
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     (arg, None, uu____6829)  in
                                   uu____6822 :: outargs  in
                                 let uu____6840 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst2, uu____6814, (arg :: arg_rets),
                                   uu____6840, fvs)
                                  in
                               tc_args head_info uu____6796 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit
                               uu____6900),Some (FStar_Syntax_Syntax.Implicit
                               uu____6901)) -> ()
                            | (None ,None ) -> ()
                            | (Some (FStar_Syntax_Syntax.Equality ),None ) ->
                                ()
                            | uu____6908 ->
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___114_6915 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___114_6915.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___114_6915.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____6917 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____6917
                             then
                               let uu____6918 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6918
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ  in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1
                                in
                             let env2 =
                               let uu___115_6923 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___115_6923.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___115_6923.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___115_6923.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___115_6923.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___115_6923.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___115_6923.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___115_6923.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___115_6923.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___115_6923.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___115_6923.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___115_6923.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___115_6923.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___115_6923.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___115_6923.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___115_6923.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___115_6923.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___115_6923.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___115_6923.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___115_6923.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___115_6923.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___115_6923.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___115_6923.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___115_6923.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___115_6923.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___115_6923.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___115_6923.FStar_TypeChecker_Env.is_native_tactic)
                               }  in
                             (let uu____6925 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High
                                 in
                              if uu____6925
                              then
                                let uu____6926 =
                                  FStar_Syntax_Print.tag_of_term e  in
                                let uu____6927 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____6928 =
                                  FStar_Syntax_Print.term_to_string targ1  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6926 uu____6927 uu____6928
                              else ());
                             (let uu____6930 = tc_term env2 e  in
                              match uu____6930 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e1, aq)  in
                                  let xterm =
                                    let uu____6947 =
                                      FStar_Syntax_Syntax.bv_to_name x1  in
                                    FStar_Syntax_Syntax.as_arg uu____6947  in
                                  let uu____6948 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name)
                                     in
                                  if uu____6948
                                  then
                                    let subst2 =
                                      let uu____6953 = FStar_List.hd bs  in
                                      maybe_extend_subst subst1 uu____6953 e1
                                       in
                                    tc_args head_info
                                      (subst2, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1, ((arg, (Some x1), c) ::
                                        outargs), (xterm :: arg_rets), g1,
                                        (x1 :: fvs)) rest rest'))))
                      | (uu____7001,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____7022) ->
                          let uu____7052 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____7052 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____7075 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____7075
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____7091 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____7091 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1))
                                             in
                                          ((let uu____7105 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____7105
                                            then
                                              let uu____7106 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____7106
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____7128 when Prims.op_Negation norm1 ->
                                     let uu____7129 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1
                                        in
                                     aux true uu____7129
                                 | uu____7130 ->
                                     let uu____7131 =
                                       let uu____7132 =
                                         let uu____7135 =
                                           let uu____7136 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead
                                              in
                                           let uu____7137 =
                                             FStar_Util.string_of_int n_args
                                              in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____7136 uu____7137
                                            in
                                         let uu____7144 =
                                           FStar_Syntax_Syntax.argpos arg  in
                                         (uu____7135, uu____7144)  in
                                       FStar_Errors.Error uu____7132  in
                                     raise uu____7131
                                  in
                               aux false chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf =
                 let uu____7157 =
                   let uu____7158 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____7158.FStar_Syntax_Syntax.n  in
                 match uu____7157 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____7166 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7230 = tc_term env1 e  in
                           (match uu____7230 with
                            | (e1,c,g_e) ->
                                let uu____7243 = tc_args1 env1 tl1  in
                                (match uu____7243 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7265 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7265)))
                        in
                     let uu____7276 = tc_args1 env args  in
                     (match uu____7276 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7298 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7318  ->
                                      match uu____7318 with
                                      | (uu____7326,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____7298
                             in
                          let ml_or_tot t r1 =
                            let uu____7342 = FStar_Options.ml_ish ()  in
                            if uu____7342
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____7345 =
                              let uu____7348 =
                                let uu____7349 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____7349
                                  FStar_Pervasives.fst
                                 in
                              FStar_TypeChecker_Util.new_uvar env uu____7348
                               in
                            ml_or_tot uu____7345 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____7358 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____7358
                            then
                              let uu____7359 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____7360 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____7361 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7359 uu____7360 uu____7361
                            else ());
                           (let uu____7364 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7364);
                           (let comp =
                              let uu____7366 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____7371  ->
                                   fun out  ->
                                     match uu____7371 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7366
                               in
                            let uu____7380 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r
                               in
                            let uu____7387 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____7380, comp, uu____7387))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7390;
                        FStar_Syntax_Syntax.tk = uu____7391;
                        FStar_Syntax_Syntax.pos = uu____7392;
                        FStar_Syntax_Syntax.vars = uu____7393;_},uu____7394)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7472 = tc_term env1 e  in
                           (match uu____7472 with
                            | (e1,c,g_e) ->
                                let uu____7485 = tc_args1 env1 tl1  in
                                (match uu____7485 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7507 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7507)))
                        in
                     let uu____7518 = tc_args1 env args  in
                     (match uu____7518 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7540 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7560  ->
                                      match uu____7560 with
                                      | (uu____7568,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____7540
                             in
                          let ml_or_tot t r1 =
                            let uu____7584 = FStar_Options.ml_ish ()  in
                            if uu____7584
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____7587 =
                              let uu____7590 =
                                let uu____7591 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____7591
                                  FStar_Pervasives.fst
                                 in
                              FStar_TypeChecker_Util.new_uvar env uu____7590
                               in
                            ml_or_tot uu____7587 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____7600 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____7600
                            then
                              let uu____7601 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____7602 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____7603 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7601 uu____7602 uu____7603
                            else ());
                           (let uu____7606 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7606);
                           (let comp =
                              let uu____7608 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____7613  ->
                                   fun out  ->
                                     match uu____7613 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7608
                               in
                            let uu____7622 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r
                               in
                            let uu____7629 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____7622, comp, uu____7629))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7644 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____7644 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1))
                             in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7680) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7686,uu____7687)
                     -> check_function_app t
                 | uu____7716 ->
                     let uu____7717 =
                       let uu____7718 =
                         let uu____7721 =
                           FStar_TypeChecker_Err.expected_function_typ env tf
                            in
                         (uu____7721, (head1.FStar_Syntax_Syntax.pos))  in
                       FStar_Errors.Error uu____7718  in
                     raise uu____7717
                  in
               check_function_app thead)

and check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)
            Prims.list ->
            FStar_Syntax_Syntax.typ option ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
                FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun g_head  ->
          fun args  ->
            fun expected_topt  ->
              let r = FStar_TypeChecker_Env.get_range env  in
              let tf =
                FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c  in
                  let uu____7776 =
                    FStar_List.fold_left2
                      (fun uu____7789  ->
                         fun uu____7790  ->
                           fun uu____7791  ->
                             match (uu____7789, uu____7790, uu____7791) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7835 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____7835 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____7847 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7847 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7849 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____7849) &&
                                              (let uu____7850 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____7850))
                                          in
                                       let uu____7851 =
                                         let uu____7857 =
                                           let uu____7863 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____7863]  in
                                         FStar_List.append seen uu____7857
                                          in
                                       let uu____7868 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____7851, uu____7868, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____7776 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____7897 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____7897
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____7899 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard
                          in
                       (match uu____7899 with | (c2,g) -> (e, c2, g)))
              | uu____7911 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.withinfo_t *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) ->
        ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term option *
          FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term *
          FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t)
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____7933 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____7933 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7959 = branch1  in
            (match uu____7959 with
             | (cpat,uu____7979,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____8017 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                      in
                   match uu____8017 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____8034 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____8034
                         then
                           let uu____8035 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____8036 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____8035 uu____8036
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____8039 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____8039 with
                         | (env1,uu____8050) ->
                             let env11 =
                               let uu___116_8054 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___116_8054.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___116_8054.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___116_8054.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___116_8054.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___116_8054.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___116_8054.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___116_8054.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___116_8054.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___116_8054.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___116_8054.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___116_8054.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___116_8054.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___116_8054.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___116_8054.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___116_8054.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___116_8054.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___116_8054.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___116_8054.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___116_8054.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___116_8054.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___116_8054.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___116_8054.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___116_8054.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___116_8054.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___116_8054.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___116_8054.FStar_TypeChecker_Env.is_native_tactic)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             ((let uu____8057 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High
                                  in
                               if uu____8057
                               then
                                 let uu____8058 =
                                   FStar_Syntax_Print.term_to_string exp  in
                                 let uu____8059 =
                                   FStar_Syntax_Print.term_to_string pat_t
                                    in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____8058 uu____8059
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t
                                  in
                               let uu____8062 = tc_tot_or_gtot_term env12 exp
                                  in
                               match uu____8062 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___117_8076 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___117_8076.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___117_8076.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___117_8076.FStar_TypeChecker_Env.implicits)
                                     }  in
                                   let uu____8077 =
                                     let g' =
                                       FStar_TypeChecker_Rel.teq env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t
                                        in
                                     let g2 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g'
                                        in
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____8081 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2
                                        in
                                     FStar_All.pipe_right uu____8081
                                       FStar_TypeChecker_Rel.resolve_implicits
                                      in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1
                                      in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp  in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t
                                      in
                                   ((let uu____8092 =
                                       let uu____8093 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2
                                          in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____8093
                                        in
                                     if uu____8092
                                     then
                                       let unresolved =
                                         let uu____8100 =
                                           FStar_Util.set_difference uvs1
                                             uvs2
                                            in
                                         FStar_All.pipe_right uu____8100
                                           FStar_Util.set_elements
                                          in
                                       let uu____8114 =
                                         let uu____8115 =
                                           let uu____8118 =
                                             let uu____8119 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp
                                                in
                                             let uu____8120 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t
                                                in
                                             let uu____8121 =
                                               let uu____8122 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____8130  ->
                                                         match uu____8130
                                                         with
                                                         | (u,uu____8134) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8122
                                                 (FStar_String.concat ", ")
                                                in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____8119 uu____8120
                                               uu____8121
                                              in
                                           (uu____8118,
                                             (p.FStar_Syntax_Syntax.p))
                                            in
                                         FStar_Errors.Error uu____8115  in
                                       raise uu____8114
                                     else ());
                                    (let uu____8138 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High
                                        in
                                     if uu____8138
                                     then
                                       let uu____8139 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1
                                          in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____8139
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1
                                        in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp)))))))
                    in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____8147 =
                   let uu____8151 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____8151
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____8147 with
                  | (scrutinee_env,uu____8164) ->
                      let uu____8167 = tc_pat true pat_t pattern  in
                      (match uu____8167 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____8189 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____8204 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____8204
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____8212 =
                                      let uu____8216 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool
                                         in
                                      tc_term uu____8216 e  in
                                    match uu____8212 with
                                    | (e1,c,g) -> ((Some e1), g))
                              in
                           (match uu____8189 with
                            | (when_clause1,g_when) ->
                                let uu____8236 = tc_term pat_env branch_exp
                                   in
                                (match uu____8236 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____8255 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_40  -> Some _0_40)
                                             uu____8255
                                        in
                                     let uu____8257 =
                                       let eqs =
                                         let uu____8263 =
                                           let uu____8264 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____8264  in
                                         if uu____8263
                                         then None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp
                                               in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____8269 -> None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8278 -> None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8279 -> None
                                            | uu____8280 ->
                                                let uu____8281 =
                                                  let uu____8282 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8282 pat_t
                                                    scrutinee_tm e
                                                   in
                                                Some uu____8281)
                                          in
                                       let uu____8283 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch
                                          in
                                       match uu____8283 with
                                       | (c1,g_branch1) ->
                                           let uu____8293 =
                                             match (eqs, when_condition) with
                                             | uu____8300 when
                                                 let uu____8305 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation uu____8305
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf
                                                    in
                                                 let uu____8313 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____8314 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____8313, uu____8314)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____8321 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8321
                                                    in
                                                 let uu____8322 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____8323 =
                                                   let uu____8324 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8324 g_when
                                                    in
                                                 (uu____8322, uu____8323)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let uu____8330 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____8330, g_when)
                                              in
                                           (match uu____8293 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let uu____8338 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak
                                                   in
                                                let uu____8339 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak
                                                   in
                                                (uu____8338, uu____8339,
                                                  g_branch1))
                                        in
                                     (match uu____8257 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8352 =
                                              let uu____8353 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____8353
                                               in
                                            if uu____8352
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8384 =
                                                     let uu____8385 =
                                                       let uu____8386 =
                                                         let uu____8388 =
                                                           let uu____8392 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8392
                                                            in
                                                         snd uu____8388  in
                                                       FStar_List.length
                                                         uu____8386
                                                        in
                                                     uu____8385 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____8384
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____8402 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____8402 with
                                                     | None  -> []
                                                     | uu____8413 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None
                                                            in
                                                         let disc1 =
                                                           let uu____8423 =
                                                             let uu____8424 =
                                                               let uu____8425
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____8425]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8424
                                                              in
                                                           uu____8423 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____8430 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool
                                                            in
                                                         [uu____8430]
                                                   else []  in
                                                 let fail uu____8438 =
                                                   let uu____8439 =
                                                     let uu____8440 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____8441 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1
                                                        in
                                                     let uu____8442 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8440 uu____8441
                                                       uu____8442
                                                      in
                                                   failwith uu____8439  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8463) ->
                                                       head_constructor t1
                                                   | uu____8469 -> fail ()
                                                    in
                                                 let pat_exp2 =
                                                   let uu____8472 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____8472
                                                     FStar_Syntax_Util.unmeta
                                                    in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____8474 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____8483;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8484;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8485;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8486;_},uu____8487)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8510 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____8512 =
                                                       let uu____8513 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8513
                                                         scrutinee_tm1
                                                         pat_exp2
                                                        in
                                                     [uu____8512]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8514 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____8524 =
                                                       let uu____8525 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____8525
                                                        in
                                                     if uu____8524
                                                     then []
                                                     else
                                                       (let uu____8532 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8532)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8538 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____8544 =
                                                       let uu____8545 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____8545
                                                        in
                                                     if uu____8544
                                                     then []
                                                     else
                                                       (let uu____8552 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8552)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____8579 =
                                                       let uu____8580 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____8580
                                                        in
                                                     if uu____8579
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8589 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8605
                                                                     ->
                                                                    match uu____8605
                                                                    with
                                                                    | 
                                                                    (ei,uu____8612)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____8622
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____8622
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8633
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8642
                                                                    =
                                                                    let uu____8643
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None  in
                                                                    let uu____8648
                                                                    =
                                                                    let uu____8649
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____8649]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8643
                                                                    uu____8648
                                                                     in
                                                                    uu____8642
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____8589
                                                            FStar_List.flatten
                                                           in
                                                        let uu____8661 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____8661
                                                          sub_term_guards)
                                                 | uu____8665 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8677 =
                                                   let uu____8678 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____8678
                                                    in
                                                 if uu____8677
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8681 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8681
                                                       in
                                                    let uu____8684 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____8684 with
                                                    | (k,uu____8688) ->
                                                        let uu____8689 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____8689
                                                         with
                                                         | (t1,uu____8694,uu____8695)
                                                             -> t1))
                                                  in
                                               let branch_guard =
                                                 build_and_check_branch_guard
                                                   scrutinee_tm norm_pat_exp
                                                  in
                                               let branch_guard1 =
                                                 match when_condition with
                                                 | None  -> branch_guard
                                                 | Some w ->
                                                     FStar_Syntax_Util.mk_conj
                                                       branch_guard w
                                                  in
                                               branch_guard1)
                                             in
                                          let guard =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when1 g_branch1
                                             in
                                          ((let uu____8701 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____8701
                                            then
                                              let uu____8702 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8702
                                            else ());
                                           (let uu____8704 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            (uu____8704, branch_guard, c1,
                                              guard)))))))))

and check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____8722 = check_let_bound_def true env1 lb  in
          (match uu____8722 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8736 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____8745 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____8745, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8748 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____8748
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____8750 =
                      let uu____8755 =
                        let uu____8761 =
                          let uu____8766 =
                            let uu____8774 = c1.FStar_Syntax_Syntax.comp ()
                               in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8774)
                             in
                          [uu____8766]  in
                        FStar_TypeChecker_Util.generalize env1 uu____8761  in
                      FStar_List.hd uu____8755  in
                    match uu____8750 with
                    | (uu____8803,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11)))
                  in
               (match uu____8736 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8814 =
                      let uu____8819 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____8819
                      then
                        let uu____8824 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____8824 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8841 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.warn uu____8841
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8842 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____8842, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8860 = c11.FStar_Syntax_Syntax.comp ()
                               in
                            FStar_All.pipe_right uu____8860
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1)
                             in
                          let e21 =
                            let uu____8868 = FStar_Syntax_Util.is_pure_comp c
                               in
                            if uu____8868
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos
                             in
                          (e21, c)))
                       in
                    (match uu____8814 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_TypeChecker_Common.t_unit
                            in
                         (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                            (Some
                               (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                          (let lb1 =
                             FStar_Syntax_Util.close_univs_and_mk_letbinding
                               None lb.FStar_Syntax_Syntax.lbname univ_vars2
                               (FStar_Syntax_Util.comp_result c12)
                               (FStar_Syntax_Util.comp_effect_name c12) e11
                              in
                           let uu____8900 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos
                              in
                           (uu____8900,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8919 -> failwith "Impossible"

and check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___118_8940 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___118_8940.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___118_8940.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___118_8940.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___118_8940.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___118_8940.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___118_8940.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___118_8940.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___118_8940.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___118_8940.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___118_8940.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___118_8940.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___118_8940.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___118_8940.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___118_8940.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___118_8940.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___118_8940.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___118_8940.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___118_8940.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___118_8940.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___118_8940.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___118_8940.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___118_8940.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___118_8940.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___118_8940.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___118_8940.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___118_8940.FStar_TypeChecker_Env.is_native_tactic)
            }  in
          let uu____8941 =
            let uu____8947 =
              let uu____8948 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____8948 FStar_Pervasives.fst  in
            check_let_bound_def false uu____8947 lb  in
          (match uu____8941 with
           | (e1,uu____8960,c1,g1,annotated) ->
               let x =
                 let uu___119_8965 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___119_8965.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___119_8965.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 }  in
               let uu____8966 =
                 let uu____8969 =
                   let uu____8970 = FStar_Syntax_Syntax.mk_binder x  in
                   [uu____8970]  in
                 FStar_Syntax_Subst.open_term uu____8969 e2  in
               (match uu____8966 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb  in
                    let x1 = fst xbinder  in
                    let uu____8982 =
                      let uu____8986 = FStar_TypeChecker_Env.push_bv env2 x1
                         in
                      tc_term uu____8986 e21  in
                    (match uu____8982 with
                     | (e22,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.bind
                             e1.FStar_Syntax_Syntax.pos env2 (Some e1) c1
                             ((Some x1), c2)
                            in
                         let e11 =
                           FStar_TypeChecker_Util.maybe_lift env2 e1
                             c1.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.eff_name
                             c1.FStar_Syntax_Syntax.res_typ
                            in
                         let e23 =
                           FStar_TypeChecker_Util.maybe_lift env2 e22
                             c2.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.eff_name
                             c2.FStar_Syntax_Syntax.res_typ
                            in
                         let lb1 =
                           FStar_Syntax_Util.mk_letbinding
                             (FStar_Util.Inl x1) []
                             c1.FStar_Syntax_Syntax.res_typ
                             c1.FStar_Syntax_Syntax.eff_name e11
                            in
                         let e3 =
                           let uu____9001 =
                             let uu____9004 =
                               let uu____9005 =
                                 let uu____9013 =
                                   FStar_Syntax_Subst.close xb e23  in
                                 ((false, [lb1]), uu____9013)  in
                               FStar_Syntax_Syntax.Tm_let uu____9005  in
                             FStar_Syntax_Syntax.mk uu____9004  in
                           uu____9001
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos
                            in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ
                            in
                         let x_eq_e1 =
                           let uu____9028 =
                             let uu____9029 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ
                                in
                             let uu____9030 =
                               FStar_Syntax_Syntax.bv_to_name x1  in
                             FStar_Syntax_Util.mk_eq2 uu____9029
                               c1.FStar_Syntax_Syntax.res_typ uu____9030 e11
                              in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_TypeChecker_Common.NonTrivial _0_41)
                             uu____9028
                            in
                         let g21 =
                           let uu____9032 =
                             let uu____9033 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard uu____9033 g2
                              in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____9032
                            in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                            in
                         let uu____9035 =
                           let uu____9036 =
                             FStar_TypeChecker_Env.expected_typ env2  in
                           FStar_Option.isSome uu____9036  in
                         if uu____9035
                         then
                           let tt =
                             let uu____9042 =
                               FStar_TypeChecker_Env.expected_typ env2  in
                             FStar_All.pipe_right uu____9042 FStar_Option.get
                              in
                           ((let uu____9046 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____9046
                             then
                               let uu____9047 =
                                 FStar_Syntax_Print.term_to_string tt  in
                               let uu____9048 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____9047 uu____9048
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ
                               in
                            (let uu____9053 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____9053
                             then
                               let uu____9054 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               let uu____9055 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____9054 uu____9055
                             else ());
                            (e4,
                              ((let uu___120_9057 = cres  in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___120_9057.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___120_9057.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___120_9057.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____9058 -> failwith "Impossible"

and check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____9079 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____9079 with
           | (lbs1,e21) ->
               let uu____9090 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____9090 with
                | (env0,topt) ->
                    let uu____9101 = build_let_rec_env true env0 lbs1  in
                    (match uu____9101 with
                     | (lbs2,rec_env) ->
                         let uu____9112 = check_let_recs rec_env lbs2  in
                         (match uu____9112 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____9124 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____9124
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____9128 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____9128
                                  (fun _0_42  -> Some _0_42)
                                 in
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
                                              lb.FStar_Syntax_Syntax.lbdef
                                             in
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
                                     let uu____9153 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____9175 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____9175)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____9153
                                      in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____9195  ->
                                           match uu____9195 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e)))
                                 in
                              let cres =
                                let uu____9220 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____9220
                                 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____9229 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21
                                   in
                                match uu____9229 with
                                | (lbs5,e22) ->
                                    ((let uu____9241 =
                                        FStar_TypeChecker_Rel.discharge_guard
                                          env1 g_lbs1
                                         in
                                      FStar_All.pipe_right uu____9241
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1));
                                     (let uu____9242 =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_let
                                              ((true, lbs5), e22)))
                                          (Some
                                             (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      (uu____9242, cres,
                                        FStar_TypeChecker_Rel.trivial_guard)))))))))
      | uu____9259 -> failwith "Impossible"

and check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____9280 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____9280 with
           | (lbs1,e21) ->
               let uu____9291 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____9291 with
                | (env0,topt) ->
                    let uu____9302 = build_let_rec_env false env0 lbs1  in
                    (match uu____9302 with
                     | (lbs2,rec_env) ->
                         let uu____9313 = check_let_recs rec_env lbs2  in
                         (match uu____9313 with
                          | (lbs3,g_lbs) ->
                              let uu____9324 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___121_9335 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___121_9335.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___121_9335.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___122_9337 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___122_9337.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___122_9337.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___122_9337.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___122_9337.FStar_Syntax_Syntax.lbdef)
                                            }  in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp))
                                             in
                                          (env3, lb1)) env1)
                                 in
                              (match uu____9324 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____9354 = tc_term env2 e21  in
                                   (match uu____9354 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9365 =
                                            let uu____9366 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9366 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9365
                                           in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres
                                           in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ
                                           in
                                        let cres2 =
                                          let uu___123_9370 = cres1  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___123_9370.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___123_9370.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___123_9370.FStar_Syntax_Syntax.comp)
                                          }  in
                                        let uu____9371 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____9371 with
                                         | (lbs5,e23) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos
                                                in
                                             (match topt with
                                              | Some uu____9400 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres
                                                     in
                                                  let cres3 =
                                                    let uu___124_9405 = cres2
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___124_9405.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___124_9405.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___124_9405.FStar_Syntax_Syntax.comp)
                                                    }  in
                                                  (e, cres3, guard)))))))))
      | uu____9408 -> failwith "Impossible"

and build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t)
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
          let uu____9431 =
            let uu____9434 =
              let uu____9435 = FStar_Syntax_Subst.compress t  in
              uu____9435.FStar_Syntax_Syntax.n  in
            let uu____9438 =
              let uu____9439 = FStar_Syntax_Subst.compress lbdef  in
              uu____9439.FStar_Syntax_Syntax.n  in
            (uu____9434, uu____9438)  in
          match uu____9431 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9445,uu____9446)) ->
              let actuals1 =
                let uu____9470 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp  in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9470
                  actuals
                 in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1  in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____9495 = FStar_Util.string_of_int n1  in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9495)
                     in
                  let formals_msg =
                    let n1 = FStar_List.length formals  in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____9513 = FStar_Util.string_of_int n1  in
                       FStar_Util.format1 "%s arguments" uu____9513)
                     in
                  let msg =
                    let uu____9521 = FStar_Syntax_Print.term_to_string lbtyp
                       in
                    let uu____9522 =
                      FStar_Syntax_Print.lbname_to_string lbname  in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9521 uu____9522 formals_msg actuals_msg
                     in
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____9527 ->
              let uu____9530 =
                let uu____9531 =
                  let uu____9534 =
                    let uu____9535 = FStar_Syntax_Print.term_to_string lbdef
                       in
                    let uu____9536 = FStar_Syntax_Print.term_to_string lbtyp
                       in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9535 uu____9536
                     in
                  (uu____9534, (lbtyp.FStar_Syntax_Syntax.pos))  in
                FStar_Errors.Error uu____9531  in
              raise uu____9530
           in
        let uu____9537 =
          FStar_List.fold_left
            (fun uu____9544  ->
               fun lb  ->
                 match uu____9544 with
                 | (lbs1,env1) ->
                     let uu____9556 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____9556 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let t1 =
                            if Prims.op_Negation check_t
                            then t
                            else
                              (let uu____9570 =
                                 let uu____9574 =
                                   let uu____9575 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left FStar_Pervasives.fst
                                     uu____9575
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___125_9580 = env0  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___125_9580.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___125_9580.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___125_9580.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___125_9580.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___125_9580.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___125_9580.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___125_9580.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___125_9580.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___125_9580.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___125_9580.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___125_9580.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___125_9580.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___125_9580.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___125_9580.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___125_9580.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___125_9580.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___125_9580.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___125_9580.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___125_9580.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___125_9580.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___125_9580.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___125_9580.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___125_9580.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___125_9580.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___125_9580.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___125_9580.FStar_TypeChecker_Env.is_native_tactic)
                                    }) t uu____9574
                                  in
                               match uu____9570 with
                               | (t1,uu____9582,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let uu____9586 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9586);
                                    norm env0 t1))
                             in
                          let env3 =
                            let uu____9588 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2)
                               in
                            if uu____9588
                            then
                              let uu___126_9589 = env2  in
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
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___126_9589.FStar_TypeChecker_Env.top_level);
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
                                  (uu___126_9589.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___126_9589.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___126_9589.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___126_9589.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1)
                             in
                          let lb1 =
                            let uu___127_9599 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___127_9599.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___127_9599.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____9537 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9613 =
        let uu____9618 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9630 =
                     let uu____9631 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef
                        in
                     uu____9631.FStar_Syntax_Syntax.n  in
                   match uu____9630 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9634 -> ()
                   | uu____9644 ->
                       let uu____9645 =
                         let uu____9646 =
                           let uu____9649 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           ("Only function literals may be defined recursively",
                             uu____9649)
                            in
                         FStar_Errors.Error uu____9646  in
                       raise uu____9645);
                  (let uu____9650 =
                     let uu____9654 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp
                        in
                     tc_tot_or_gtot_term uu____9654
                       lb.FStar_Syntax_Syntax.lbdef
                      in
                   match uu____9650 with
                   | (e,c,g) ->
                       ((let uu____9661 =
                           let uu____9662 =
                             FStar_Syntax_Util.is_total_lcomp c  in
                           Prims.op_Negation uu____9662  in
                         if uu____9661
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
                             FStar_Syntax_Const.effect_Tot_lid e
                            in
                         (lb1, g))))))
           in
        FStar_All.pipe_right uu____9618 FStar_List.unzip  in
      match uu____9613 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs
              FStar_TypeChecker_Rel.trivial_guard
             in
          (lbs1, g_lbs)

and check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t *
          Prims.bool)
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____9691 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____9691 with
        | (env1,uu____9701) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____9707 = check_lbtyp top_level env lb  in
            (match uu____9707 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____9733 =
                     tc_maybe_toplevel_term
                       (let uu___128_9737 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___128_9737.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___128_9737.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___128_9737.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___128_9737.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___128_9737.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___128_9737.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___128_9737.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___128_9737.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___128_9737.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___128_9737.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___128_9737.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___128_9737.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___128_9737.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___128_9737.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___128_9737.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___128_9737.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___128_9737.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___128_9737.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___128_9737.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___128_9737.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___128_9737.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___128_9737.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___128_9737.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___128_9737.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___128_9737.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___128_9737.FStar_TypeChecker_Env.is_native_tactic)
                        }) e11
                      in
                   match uu____9733 with
                   | (e12,c1,g1) ->
                       let uu____9746 =
                         let uu____9749 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9752  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9749 e12 c1 wf_annot
                          in
                       (match uu____9746 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____9762 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____9762
                              then
                                let uu____9763 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____9764 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____9765 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9763 uu____9764 uu____9765
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))

and check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ option * FStar_TypeChecker_Env.guard_t *
          FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.subst_elt
          Prims.list * FStar_TypeChecker_Env.env)
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            (if lb.FStar_Syntax_Syntax.lbunivs <> []
             then
               failwith
                 "Impossible: non-empty universe variables but the type is unknown"
             else ();
             (None, FStar_TypeChecker_Rel.trivial_guard, [], [], env))
        | uu____9791 ->
            let uu____9792 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____9792 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9819 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9819)
                 else
                   (let uu____9824 = FStar_Syntax_Util.type_u ()  in
                    match uu____9824 with
                    | (k,uu____9835) ->
                        let uu____9836 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____9836 with
                         | (t2,uu____9848,g) ->
                             ((let uu____9851 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____9851
                               then
                                 let uu____9852 =
                                   let uu____9853 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____9853  in
                                 let uu____9854 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9852 uu____9854
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____9857 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9857))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9862  ->
      match uu____9862 with
      | (x,imp) ->
          let uu____9873 = FStar_Syntax_Util.type_u ()  in
          (match uu____9873 with
           | (tu,u) ->
               ((let uu____9885 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____9885
                 then
                   let uu____9886 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____9887 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____9888 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9886 uu____9887 uu____9888
                 else ());
                (let uu____9890 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____9890 with
                 | (t,uu____9901,g) ->
                     let x1 =
                       ((let uu___129_9906 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___129_9906.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___129_9906.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____9908 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____9908
                       then
                         let uu____9909 =
                           FStar_Syntax_Print.bv_to_string (fst x1)  in
                         let uu____9910 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9909 uu____9910
                       else ());
                      (let uu____9912 = push_binding env x1  in
                       (x1, uu____9912, g, u))))))

and tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe Prims.list)
  =
  fun env  ->
    fun bs  ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> ([], env1, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs2 ->
            let uu____9963 = tc_binder env1 b  in
            (match uu____9963 with
             | (b1,env',g,u) ->
                 let uu____9986 = aux env' bs2  in
                 (match uu____9986 with
                  | (bs3,env'1,g',us) ->
                      let uu____10015 =
                        let uu____10016 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g uu____10016  in
                      ((b1 :: bs3), env'1, uu____10015, (u :: us))))
         in
      aux env bs

and tc_pats :
  FStar_TypeChecker_Env.env ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list
      Prims.list ->
      (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____10059  ->
             fun uu____10060  ->
               match (uu____10059, uu____10060) with
               | ((t,imp),(args1,g)) ->
                   let uu____10097 = tc_term env1 t  in
                   (match uu____10097 with
                    | (t1,uu____10107,g') ->
                        let uu____10109 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____10109))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____10127  ->
             match uu____10127 with
             | (pats1,g) ->
                 let uu____10141 = tc_args env p  in
                 (match uu____10141 with
                  | (args,g') ->
                      let uu____10149 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____10149))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____10157 = tc_maybe_toplevel_term env e  in
      match uu____10157 with
      | (e1,c,g) ->
          let uu____10167 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____10167
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = c.FStar_Syntax_Syntax.comp ()  in
             let c2 = norm_c env c1  in
             let uu____10177 =
               let uu____10180 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____10180
               then
                 let uu____10183 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____10183, false)
               else
                 (let uu____10185 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____10185, true))
                in
             match uu____10177 with
             | (target_comp,allow_ghost) ->
                 let uu____10191 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____10191 with
                  | Some g' ->
                      let uu____10197 =
                        FStar_TypeChecker_Rel.conj_guard g1 g'  in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____10197)
                  | uu____10198 ->
                      if allow_ghost
                      then
                        let uu____10203 =
                          let uu____10204 =
                            let uu____10207 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2
                               in
                            (uu____10207, (e1.FStar_Syntax_Syntax.pos))  in
                          FStar_Errors.Error uu____10204  in
                        raise uu____10203
                      else
                        (let uu____10212 =
                           let uu____10213 =
                             let uu____10216 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2
                                in
                             (uu____10216, (e1.FStar_Syntax_Syntax.pos))  in
                           FStar_Errors.Error uu____10213  in
                         raise uu____10212)))

and tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
        tc_tot_or_gtot_term env1 e

and tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun t  ->
      let uu____10229 = tc_tot_or_gtot_term env t  in
      match uu____10229 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      (let uu____10251 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____10251
       then
         let uu____10252 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____10252
       else ());
      (let env1 =
         let uu___130_10255 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___130_10255.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___130_10255.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___130_10255.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___130_10255.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___130_10255.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___130_10255.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___130_10255.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___130_10255.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___130_10255.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___130_10255.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___130_10255.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___130_10255.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___130_10255.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___130_10255.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___130_10255.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___130_10255.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___130_10255.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___130_10255.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___130_10255.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___130_10255.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___130_10255.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___130_10255.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___130_10255.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___130_10255.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___130_10255.FStar_TypeChecker_Env.is_native_tactic)
         }  in
       let uu____10258 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10274) ->
             let uu____10275 =
               let uu____10276 =
                 let uu____10279 = FStar_TypeChecker_Env.get_range env1  in
                 ((Prims.strcat "Implicit argument: " msg), uu____10279)  in
               FStar_Errors.Error uu____10276  in
             raise uu____10275
          in
       match uu____10258 with
       | (t,c,g) ->
           let uu____10289 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____10289
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10296 =
                let uu____10297 =
                  let uu____10300 =
                    let uu____10301 = FStar_Syntax_Print.term_to_string e  in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10301
                     in
                  let uu____10302 = FStar_TypeChecker_Env.get_range env1  in
                  (uu____10300, uu____10302)  in
                FStar_Errors.Error uu____10297  in
              raise uu____10296))
  
let level_of_type_fail env e t =
  let uu____10327 =
    let uu____10328 =
      let uu____10331 =
        let uu____10332 = FStar_Syntax_Print.term_to_string e  in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10332 t
         in
      let uu____10333 = FStar_TypeChecker_Env.get_range env  in
      (uu____10331, uu____10333)  in
    FStar_Errors.Error uu____10328  in
  raise uu____10327 
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____10353 =
            let uu____10354 = FStar_Syntax_Util.unrefine t1  in
            uu____10354.FStar_Syntax_Syntax.n  in
          match uu____10353 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10358 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____10361 = FStar_Syntax_Util.type_u ()  in
                 match uu____10361 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___133_10367 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___133_10367.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___133_10367.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___133_10367.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___133_10367.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___133_10367.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___133_10367.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___133_10367.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___133_10367.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___133_10367.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___133_10367.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___133_10367.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___133_10367.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___133_10367.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___133_10367.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___133_10367.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___133_10367.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___133_10367.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___133_10367.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___133_10367.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___133_10367.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___133_10367.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___133_10367.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___133_10367.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___133_10367.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___133_10367.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___133_10367.FStar_TypeChecker_Env.is_native_tactic)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____10371 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____10371
                       | uu____10372 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u))
           in
        aux true t
  
let rec universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun e  ->
      let uu____10383 =
        let uu____10384 = FStar_Syntax_Subst.compress e  in
        uu____10384.FStar_Syntax_Syntax.n  in
      match uu____10383 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10389 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10394 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10411 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10422) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10437,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10452) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10459 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10459 with | ((uu____10470,t),uu____10472) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10475,(FStar_Util.Inl t,uu____10477),uu____10478) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10514,(FStar_Util.Inr c,uu____10516),uu____10517) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)) None
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10560;
             FStar_Syntax_Syntax.pos = uu____10561;
             FStar_Syntax_Syntax.vars = uu____10562;_},us)
          ->
          let uu____10568 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10568 with
           | ((us',t),uu____10581) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10593 =
                     let uu____10594 =
                       let uu____10597 = FStar_TypeChecker_Env.get_range env
                          in
                       ("Unexpected number of universe instantiations",
                         uu____10597)
                        in
                     FStar_Errors.Error uu____10594  in
                   raise uu____10593)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10604 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10605 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10613) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10630 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____10630 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10641  ->
                      match uu____10641 with
                      | (b,uu____10645) ->
                          let uu____10646 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10646) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____10651 = universe_of_aux env res  in
                 level_of_type env res uu____10651  in
               let u_c =
                 let uu____10653 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____10653 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10656 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____10656
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u) None
                 e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2  in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____10726 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10736 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10760 ->
                let uu____10761 = universe_of_aux env hd3  in
                (uu____10761, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10771 ->
                let uu____10772 = universe_of_aux env hd3  in
                (uu____10772, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10782 ->
                let uu____10791 = universe_of_aux env hd3  in
                (uu____10791, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10801 ->
                let uu____10806 = universe_of_aux env hd3  in
                (uu____10806, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10816 ->
                let uu____10834 = universe_of_aux env hd3  in
                (uu____10834, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10844 ->
                let uu____10849 = universe_of_aux env hd3  in
                (uu____10849, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10859 ->
                let uu____10860 = universe_of_aux env hd3  in
                (uu____10860, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10870 ->
                let uu____10878 = universe_of_aux env hd3  in
                (uu____10878, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____10888 ->
                let uu____10893 = universe_of_aux env hd3  in
                (uu____10893, args1)
            | FStar_Syntax_Syntax.Tm_type uu____10903 ->
                let uu____10904 = universe_of_aux env hd3  in
                (uu____10904, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10914,hd4::uu____10916) ->
                let uu____10963 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____10963 with
                 | (uu____10973,uu____10974,hd5) ->
                     let uu____10990 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____10990 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____11025 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____11027 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____11027 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____11062 ->
                let uu____11063 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____11063 with
                 | (env1,uu____11077) ->
                     let env2 =
                       let uu___134_11081 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___134_11081.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___134_11081.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___134_11081.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___134_11081.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___134_11081.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___134_11081.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___134_11081.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___134_11081.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___134_11081.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___134_11081.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___134_11081.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___134_11081.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___134_11081.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___134_11081.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___134_11081.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___134_11081.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___134_11081.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___134_11081.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___134_11081.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___134_11081.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___134_11081.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___134_11081.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___134_11081.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___134_11081.FStar_TypeChecker_Env.is_native_tactic)
                       }  in
                     ((let uu____11083 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____11083
                       then
                         let uu____11084 =
                           let uu____11085 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____11085  in
                         let uu____11086 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____11084 uu____11086
                       else ());
                      (let uu____11088 = tc_term env2 hd3  in
                       match uu____11088 with
                       | (uu____11101,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____11102;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____11104;
                                        FStar_Syntax_Syntax.comp =
                                          uu____11105;_},g)
                           ->
                           ((let uu____11115 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____11115
                               FStar_Pervasives.ignore);
                            (t, args1)))))
             in
          let uu____11123 = type_of_head true hd1 args  in
          (match uu____11123 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____11152 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____11152 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____11189 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____11189)))
      | FStar_Syntax_Syntax.Tm_match (uu____11192,hd1::uu____11194) ->
          let uu____11241 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____11241 with
           | (uu____11244,uu____11245,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11261,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____11297 = universe_of_aux env e  in
      level_of_type env e uu____11297
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____11312 = tc_binders env tps  in
      match uu____11312 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
  