open Prims
let instantiate_both : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___82_4 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___82_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___82_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___82_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___82_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___82_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___82_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___82_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___82_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___82_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___82_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___82_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___82_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___82_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___82_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___82_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___82_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___82_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___82_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___82_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___82_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___82_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___82_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___82_4.FStar_TypeChecker_Env.qname_and_index)
    }
  
let no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___83_8 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___83_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___83_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___83_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___83_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___83_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___83_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___83_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___83_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___83_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___83_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___83_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___83_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___83_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___83_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___83_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___83_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___83_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___83_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___83_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___83_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___83_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___83_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___83_8.FStar_TypeChecker_Env.qname_and_index)
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
           let uu____34 =
             let uu____35 =
               let uu____36 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____37 =
                 let uu____39 = FStar_Syntax_Syntax.as_arg tl1  in [uu____39]
                  in
               uu____36 :: uu____37  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____35
              in
           uu____34 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)
      vs FStar_Syntax_Util.lex_top
  
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.bool =
  fun uu___77_47  ->
    match uu___77_47 with
    | Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____49 -> false
  
let steps env =
  [FStar_TypeChecker_Normalize.Beta;
  FStar_TypeChecker_Normalize.Eager_unfolding] 
let unfold_whnf :
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
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____106 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
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
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____116
                            | Some head1 ->
                                let uu____118 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____119 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____118 uu____119
                             in
                          let uu____120 =
                            let uu____121 =
                              let uu____124 =
                                FStar_TypeChecker_Env.get_range env  in
                              (msg, uu____124)  in
                            FStar_Errors.Error uu____121  in
                          Prims.raise uu____120  in
                        let s =
                          let uu____126 =
                            let uu____127 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left Prims.fst uu____127  in
                          FStar_TypeChecker_Util.new_uvar env uu____126  in
                        let uu____132 =
                          FStar_TypeChecker_Rel.try_teq env t1 s  in
                        match uu____132 with
                        | Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____136 -> fail ()))
             in
          aux false kt
  
let push_binding env b = FStar_TypeChecker_Env.push_bv env (Prims.fst b) 
let maybe_extend_subst :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.subst_t
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____167 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____167
        then s
        else (FStar_Syntax_Syntax.NT ((Prims.fst b), v1)) :: s
  
let set_lcomp_result :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun t  ->
        let uu___84_184 = lc  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (uu___84_184.FStar_Syntax_Syntax.lcomp_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (uu___84_184.FStar_Syntax_Syntax.lcomp_univs);
          FStar_Syntax_Syntax.lcomp_indices =
            (uu___84_184.FStar_Syntax_Syntax.lcomp_indices);
          FStar_Syntax_Syntax.lcomp_res_typ = t;
          FStar_Syntax_Syntax.lcomp_cflags =
            (uu___84_184.FStar_Syntax_Syntax.lcomp_cflags);
          FStar_Syntax_Syntax.lcomp_as_comp =
            (fun uu____185  ->
               let uu____186 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
               FStar_TypeChecker_Env.set_result_typ env uu____186 t)
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
            let uu____223 =
              let uu____224 = FStar_Syntax_Subst.compress t  in
              uu____224.FStar_Syntax_Syntax.n  in
            match uu____223 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____227,c) ->
                let uu____239 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                if uu____239
                then
                  let t1 =
                    let uu____241 = FStar_TypeChecker_Env.result_typ env c
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____241
                     in
                  let uu____242 =
                    let uu____243 = FStar_Syntax_Subst.compress t1  in
                    uu____243.FStar_Syntax_Syntax.n  in
                  (match uu____242 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____247 -> false
                   | uu____248 -> true)
                else false
            | uu____250 -> true  in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____253 =
                  let uu____254 =
                    (let uu____255 = should_return t  in
                     Prims.op_Negation uu____255) ||
                      (let uu____256 =
                         FStar_TypeChecker_Env.should_verify env  in
                       Prims.op_Negation uu____256)
                     in
                  if uu____254
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e  in
                FStar_TypeChecker_Env.lcomp_of_comp env uu____253
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.lcomp_res_typ  in
          let uu____262 =
            let uu____266 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____266 with
            | None  -> let uu____271 = memo_tk e t  in (uu____271, lc, guard)
            | Some t' ->
                ((let uu____274 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High  in
                  if uu____274
                  then
                    let uu____275 = FStar_Syntax_Print.term_to_string t  in
                    let uu____276 = FStar_Syntax_Print.term_to_string t'  in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____275
                      uu____276
                  else ());
                 (let uu____278 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t'
                     in
                  match uu____278 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.lcomp_res_typ  in
                      let uu____289 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____289 with
                       | (e2,g) ->
                           ((let uu____298 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____298
                             then
                               let uu____299 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____300 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____301 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____302 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____299 uu____300 uu____301 uu____302
                             else ());
                            (let msg =
                               let uu____308 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               if uu____308
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_28  -> Some _0_28)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             let uu____323 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1
                                in
                             match uu____323 with
                             | (lc2,g2) ->
                                 let uu____331 = memo_tk e2 t'  in
                                 (uu____331, (set_lcomp_result env lc2 t'),
                                   g2))))))
             in
          match uu____262 with
          | (e1,lc1,g) ->
              ((let uu____339 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                if uu____339
                then
                  let uu____340 = FStar_Syntax_Print.lcomp_to_string lc1  in
                  FStar_Util.print1 "Return comp type is %s\n" uu____340
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
        let uu____357 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____357 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____363 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____363 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
  
let check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp Prims.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun copt  ->
      fun uu____385  ->
        match uu____385 with
        | (e,c) ->
            let expected_c_opt =
              match copt with
              | Some uu____400 -> copt
              | None  ->
                  let uu____401 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Syntax_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____402 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____402))
                     in
                  if uu____401
                  then
                    let uu____404 =
                      let uu____405 = FStar_TypeChecker_Env.result_typ env c
                         in
                      FStar_Syntax_Util.ml_comp uu____405
                        e.FStar_Syntax_Syntax.pos
                       in
                    Some uu____404
                  else
                    (let uu____407 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____407
                     then None
                     else
                       (let uu____410 = FStar_Syntax_Util.is_pure_comp c  in
                        if uu____410
                        then
                          let uu____412 =
                            let uu____413 =
                              FStar_TypeChecker_Env.result_typ env c  in
                            FStar_Syntax_Syntax.mk_Total uu____413  in
                          Some uu____412
                        else
                          (let uu____415 =
                             FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                           if uu____415
                           then
                             let uu____417 =
                               let uu____418 =
                                 FStar_TypeChecker_Env.result_typ env c  in
                               FStar_Syntax_Syntax.mk_GTotal uu____418  in
                             Some uu____417
                           else None)))
               in
            (match expected_c_opt with
             | None  ->
                 let uu____423 = norm_c env c  in
                 (e, uu____423, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____426 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                   if uu____426
                   then
                     let uu____427 = FStar_Syntax_Print.term_to_string e  in
                     let uu____428 = FStar_Syntax_Print.comp_to_string c  in
                     let uu____429 =
                       FStar_Syntax_Print.comp_to_string expected_c  in
                     FStar_Util.print3
                       "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                       uu____427 uu____428 uu____429
                   else ());
                  (let c1 = norm_c env c  in
                   (let uu____433 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                    if uu____433
                    then
                      let uu____434 = FStar_Syntax_Print.term_to_string e  in
                      let uu____435 = FStar_Syntax_Print.comp_to_string c1
                         in
                      let uu____436 =
                        FStar_Syntax_Print.comp_to_string expected_c  in
                      FStar_Util.print3
                        "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                        uu____434 uu____435 uu____436
                    else ());
                   (let uu____438 =
                      FStar_TypeChecker_Util.check_comp env e c1 expected_c
                       in
                    match uu____438 with
                    | (e1,uu____446,g) ->
                        let g1 =
                          let uu____449 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_TypeChecker_Util.label_guard uu____449
                            "could not prove post-condition" g
                           in
                        ((let uu____451 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low
                             in
                          if uu____451
                          then
                            let uu____452 =
                              FStar_Range.string_of_range
                                e1.FStar_Syntax_Syntax.pos
                               in
                            let uu____453 =
                              FStar_TypeChecker_Rel.guard_to_string env g1
                               in
                            FStar_Util.print2
                              "(%s) DONE check_expected_effect; guard is: %s\n"
                              uu____452 uu____453
                          else ());
                         (let e2 =
                            let uu____456 =
                              FStar_TypeChecker_Env.result_typ env c1  in
                            FStar_TypeChecker_Util.maybe_lift env e1
                              (FStar_Syntax_Util.comp_effect_name c1)
                              (FStar_Syntax_Util.comp_effect_name expected_c)
                              uu____456
                             in
                          (e2, expected_c, g1)))))))
  
let no_logical_guard env uu____476 =
  match uu____476 with
  | (te,kt,f) ->
      let uu____483 = FStar_TypeChecker_Rel.guard_form f  in
      (match uu____483 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____488 =
             let uu____489 =
               let uu____492 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____493 = FStar_TypeChecker_Env.get_range env  in
               (uu____492, uu____493)  in
             FStar_Errors.Error uu____489  in
           Prims.raise uu____488)
  
let print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____500 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____500 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____503 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____503
  
let check_smt_pat env t bs c =
  let uu____538 = FStar_Syntax_Util.is_smt_lemma t  in
  if uu____538
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_typ_name = uu____539;
          FStar_Syntax_Syntax.comp_univs = uu____540;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____544)::[];
          FStar_Syntax_Syntax.flags = uu____545;_}
        ->
        let pat_vars =
          let uu____577 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats
             in
          FStar_Syntax_Free.names uu____577  in
        let uu____578 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____590  ->
                  match uu____590 with
                  | (b,uu____594) ->
                      let uu____595 = FStar_Util.set_mem b pat_vars  in
                      Prims.op_Negation uu____595))
           in
        (match uu____578 with
         | None  -> ()
         | Some (x,uu____599) ->
             let uu____602 =
               let uu____603 = FStar_Syntax_Print.bv_to_string x  in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____603
                in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____602)
    | uu____604 -> failwith "Impossible"
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
        let uu____625 =
          let uu____626 = FStar_TypeChecker_Env.should_verify env  in
          Prims.op_Negation uu____626  in
        if uu____625
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env  in
               let env1 =
                 let uu___85_644 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___85_644.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___85_644.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___85_644.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___85_644.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___85_644.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___85_644.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___85_644.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___85_644.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___85_644.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___85_644.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___85_644.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___85_644.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___85_644.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___85_644.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___85_644.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___85_644.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___85_644.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___85_644.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___85_644.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___85_644.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___85_644.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___85_644.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___85_644.FStar_TypeChecker_Env.qname_and_index)
                 }  in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid
                  in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____667  ->
                           match uu____667 with
                           | (b,uu____672) ->
                               let t =
                                 let uu____674 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort
                                    in
                                 unfold_whnf env1 uu____674  in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type _
                                  |FStar_Syntax_Syntax.Tm_arrow _ -> []
                                | uu____678 ->
                                    let uu____679 =
                                      FStar_Syntax_Syntax.bv_to_name b  in
                                    [uu____679])))
                    in
                 let as_lex_list dec =
                   let uu____684 = FStar_Syntax_Util.head_and_args dec  in
                   match uu____684 with
                   | (head1,uu____695) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____711 -> mk_lex_list [dec])
                    in
                 let cflags = FStar_Syntax_Util.comp_flags c  in
                 let uu____714 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___78_718  ->
                           match uu___78_718 with
                           | FStar_Syntax_Syntax.DECREASES uu____719 -> true
                           | uu____722 -> false))
                    in
                 match uu____714 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____726 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions  in
                     (match xs with
                      | x::[] -> x
                      | uu____732 -> mk_lex_list xs)
                  in
               let previous_dec = decreases_clause actuals expected_c  in
               let guard_one_letrec uu____742 =
                 match uu____742 with
                 | (l,t) ->
                     let uu____749 =
                       let uu____750 = FStar_Syntax_Subst.compress t  in
                       uu____750.FStar_Syntax_Syntax.n  in
                     (match uu____749 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____781  ->
                                    match uu____781 with
                                    | (x,imp) ->
                                        let uu____788 =
                                          FStar_Syntax_Syntax.is_null_bv x
                                           in
                                        if uu____788
                                        then
                                          let uu____791 =
                                            let uu____792 =
                                              let uu____794 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x
                                                 in
                                              Some uu____794  in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____792
                                              x.FStar_Syntax_Syntax.sort
                                             in
                                          (uu____791, imp)
                                        else (x, imp)))
                             in
                          let uu____796 =
                            FStar_Syntax_Subst.open_comp formals1 c  in
                          (match uu____796 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1  in
                               let precedes1 =
                                 let uu____807 =
                                   let uu____808 =
                                     let uu____809 =
                                       FStar_Syntax_Syntax.as_arg dec  in
                                     let uu____810 =
                                       let uu____812 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec
                                          in
                                       [uu____812]  in
                                     uu____809 :: uu____810  in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____808
                                    in
                                 uu____807 None r  in
                               let uu____817 = FStar_Util.prefix formals2  in
                               (match uu____817 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___86_841 = last1  in
                                      let uu____842 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___86_841.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___86_841.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____842
                                      }  in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)]  in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1
                                       in
                                    ((let uu____857 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low
                                         in
                                      if uu____857
                                      then
                                        let uu____858 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l
                                           in
                                        let uu____859 =
                                          FStar_Syntax_Print.term_to_string t
                                           in
                                        let uu____860 =
                                          FStar_Syntax_Print.term_to_string
                                            t'
                                           in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____858 uu____859 uu____860
                                      else ());
                                     (l, t'))))
                      | uu____862 ->
                          Prims.raise
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
        (let uu___87_1120 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___87_1120.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___87_1120.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___87_1120.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___87_1120.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___87_1120.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___87_1120.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___87_1120.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___87_1120.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___87_1120.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___87_1120.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___87_1120.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___87_1120.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___87_1120.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___87_1120.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___87_1120.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___87_1120.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___87_1120.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___87_1120.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___87_1120.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___87_1120.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___87_1120.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___87_1120.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___87_1120.FStar_TypeChecker_Env.qname_and_index)
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
      (let uu____1129 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____1129
       then
         let uu____1130 =
           let uu____1131 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1131  in
         let uu____1132 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____1130 uu____1132
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1138 -> failwith "Impossible"
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
           let uu____1177 = tc_tot_or_gtot_term env1 e1  in
           (match uu____1177 with
            | (e2,c,g) ->
                let g1 =
                  let uu___88_1188 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___88_1188.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___88_1188.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___88_1188.FStar_TypeChecker_Env.implicits)
                  }  in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1201 = FStar_Syntax_Util.type_u ()  in
           (match uu____1201 with
            | (t,u) ->
                let uu____1209 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____1209 with
                 | (e2,c,g) ->
                     let uu____1219 =
                       let uu____1228 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____1228 with
                       | (env2,uu____1241) -> tc_pats env2 pats  in
                     (match uu____1219 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___89_1262 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___89_1262.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___89_1262.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___89_1262.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____1263 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____1274 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____1263, c, uu____1274))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1282 =
             let uu____1283 = FStar_Syntax_Subst.compress e1  in
             uu____1283.FStar_Syntax_Syntax.n  in
           (match uu____1282 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1289,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1291;
                               FStar_Syntax_Syntax.lbtyp = uu____1292;
                               FStar_Syntax_Syntax.lbeff = uu____1293;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1311 =
                  let uu____1315 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit
                     in
                  tc_term uu____1315 e11  in
                (match uu____1311 with
                 | (e12,c1,g1) ->
                     let uu____1322 = tc_term env1 e2  in
                     (match uu____1322 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind env1 (Some e12) c1
                              (None, c2)
                             in
                          let e3 =
                            let uu____1337 =
                              let uu____1340 =
                                let uu____1341 =
                                  let uu____1349 =
                                    let uu____1353 =
                                      let uu____1355 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.lcomp_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e12)
                                         in
                                      [uu____1355]  in
                                    (false, uu____1353)  in
                                  (uu____1349, e21)  in
                                FStar_Syntax_Syntax.Tm_let uu____1341  in
                              FStar_Syntax_Syntax.mk uu____1340  in
                            uu____1337
                              (Some
                                 ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                              e1.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e3,
                                    (FStar_Syntax_Syntax.Meta_desugared
                                       FStar_Syntax_Syntax.Sequence))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____1386 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e4, c, uu____1386)))
            | uu____1389 ->
                let uu____1390 = tc_term env1 e1  in
                (match uu____1390 with
                 | (e2,c,g) ->
                     let e3 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (e2,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Sequence))))
                         (Some
                            ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1414) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1429 = tc_term env1 e1  in
           (match uu____1429 with
            | (e2,c,g) ->
                let e3 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,FStar_Util.Inr expected_c,uu____1454) ->
           let uu____1473 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____1473 with
            | (env0,uu____1481) ->
                let uu____1484 = tc_comp env0 expected_c  in
                (match uu____1484 with
                 | (expected_c1,uu____1492,g) ->
                     let t_res =
                       FStar_TypeChecker_Env.result_typ env1 expected_c1  in
                     let uu____1495 =
                       let uu____1499 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____1499 e1  in
                     (match uu____1495 with
                      | (e2,c',g') ->
                          let uu____1506 =
                            let uu____1510 =
                              let uu____1513 =
                                c'.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                              (e2, uu____1513)  in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1510
                             in
                          (match uu____1506 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 (FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_ascribed
                                       (e3, (FStar_Util.Inl t_res),
                                         (Some
                                            (FStar_Syntax_Util.comp_effect_name
                                               expected_c2)))))
                                   (Some (t_res.FStar_Syntax_Syntax.n))
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let lc =
                                 FStar_TypeChecker_Env.lcomp_of_comp env1
                                   expected_c2
                                  in
                               let f =
                                 let uu____1544 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1544
                                  in
                               let uu____1545 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____1545 with
                                | (e5,c,f2) ->
                                    let uu____1555 =
                                      FStar_TypeChecker_Rel.conj_guard f f2
                                       in
                                    (e5, c, uu____1555))))))
       | FStar_Syntax_Syntax.Tm_ascribed (e1,FStar_Util.Inl t,uu____1558) ->
           let uu____1577 = FStar_Syntax_Util.type_u ()  in
           (match uu____1577 with
            | (k,u) ->
                let uu____1585 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____1585 with
                 | (t1,uu____1593,f) ->
                     let uu____1595 =
                       let uu____1599 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____1599 e1  in
                     (match uu____1595 with
                      | (e2,c,g) ->
                          let uu____1606 =
                            let uu____1609 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1612  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1609 e2 c f
                             in
                          (match uu____1606 with
                           | (c1,f1) ->
                               let uu____1618 =
                                 let uu____1622 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, (FStar_Util.Inl t1),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.lcomp_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env1 uu____1622 c1
                                  in
                               (match uu____1618 with
                                | (e3,c2,f2) ->
                                    let uu____1644 =
                                      let uu____1645 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1645
                                       in
                                    (e3, c2, uu____1644))))))
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
           let rest1 = hd1 :: rest  in
           let uu____1722 = FStar_Syntax_Util.head_and_args top  in
           (match uu____1722 with
            | (unary_op,uu____1736) ->
                let head1 =
                  let uu____1754 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (Prims.fst a).FStar_Syntax_Syntax.pos
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1754
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
              FStar_Syntax_Syntax.tk = uu____1798;
              FStar_Syntax_Syntax.pos = uu____1799;
              FStar_Syntax_Syntax.vars = uu____1800;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____1826 =
               let uu____1830 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               match uu____1830 with | (env0,uu____1838) -> tc_term env0 e1
                in
             match uu____1826 with
             | (e2,c,g) ->
                 let uu____1847 = FStar_Syntax_Util.head_and_args top  in
                 (match uu____1847 with
                  | (reify_op,uu____1861) ->
                      let repr = FStar_TypeChecker_Util.reify_comp env1 c  in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos
                         in
                      let c1 =
                        let uu____1898 = FStar_Syntax_Syntax.mk_Total repr
                           in
                        FStar_All.pipe_right uu____1898
                          (FStar_TypeChecker_Env.lcomp_of_comp env1)
                         in
                      let uu____1899 = comp_check_expected_typ env1 e3 c1  in
                      (match uu____1899 with
                       | (e4,c2,g') ->
                           let uu____1909 =
                             FStar_TypeChecker_Rel.conj_guard g g'  in
                           (e4, c2, uu____1909)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____1911;
              FStar_Syntax_Syntax.pos = uu____1912;
              FStar_Syntax_Syntax.vars = uu____1913;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____1945 =
               let uu____1946 =
                 let uu____1947 =
                   let uu____1950 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str
                      in
                   (uu____1950, (e1.FStar_Syntax_Syntax.pos))  in
                 FStar_Errors.Error uu____1947  in
               Prims.raise uu____1946  in
             let uu____1954 = FStar_Syntax_Util.head_and_args top  in
             match uu____1954 with
             | (reflect_op,uu____1968) ->
                 let uu____1983 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____1983 with
                  | None  -> no_reflect ()
                  | Some ed ->
                      let uu____1989 =
                        let uu____1990 =
                          FStar_All.pipe_right
                            ed.FStar_Syntax_Syntax.qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____1990  in
                      if uu____1989
                      then no_reflect ()
                      else
                        (let uu____1996 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____1996 with
                         | (env_no_ex,topt) ->
                             let uu____2007 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____2022 =
                                   let uu____2025 =
                                     let uu____2026 =
                                       let uu____2036 =
                                         let uu____2038 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____2039 =
                                           let uu____2041 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____2041]  in
                                         uu____2038 :: uu____2039  in
                                       (repr, uu____2036)  in
                                     FStar_Syntax_Syntax.Tm_app uu____2026
                                      in
                                   FStar_Syntax_Syntax.mk uu____2025  in
                                 uu____2022 None top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____2051 =
                                 let uu____2055 =
                                   let uu____2056 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____2056 Prims.fst
                                    in
                                 tc_tot_or_gtot_term uu____2055 t  in
                               match uu____2051 with
                               | (t1,uu____2073,g) ->
                                   let uu____2075 =
                                     let uu____2076 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____2076.FStar_Syntax_Syntax.n  in
                                   (match uu____2075 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2087,(res,uu____2089)::
                                         (wp,uu____2091)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2125 -> failwith "Impossible")
                                in
                             (match uu____2007 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2149 =
                                    let uu____2152 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____2152 with
                                    | (e2,c,g) ->
                                        ((let uu____2162 =
                                            let uu____2163 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2163
                                             in
                                          if uu____2162
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2169 =
                                            FStar_TypeChecker_Rel.try_teq
                                              env_no_ex
                                              c.FStar_Syntax_Syntax.lcomp_res_typ
                                              expected_repr_typ
                                             in
                                          match uu____2169 with
                                          | None  ->
                                              ((let uu____2174 =
                                                  let uu____2178 =
                                                    let uu____2181 =
                                                      let uu____2182 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____2183 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.lcomp_res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2182 uu____2183
                                                       in
                                                    (uu____2181,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____2178]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2174);
                                               (let uu____2188 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____2188)))
                                          | Some g' ->
                                              let uu____2190 =
                                                let uu____2191 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2191
                                                 in
                                              (e2, uu____2190)))
                                     in
                                  (match uu____2149 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2198 =
                                           let uu____2199 =
                                             let uu____2200 =
                                               let uu____2201 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____2201]  in
                                             let uu____2202 =
                                               let uu____2208 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   res_typ
                                                  in
                                               let uu____2209 =
                                                 let uu____2211 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     wp
                                                    in
                                                 [uu____2211]  in
                                               uu____2208 :: uu____2209  in
                                             {
                                               FStar_Syntax_Syntax.comp_typ_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2200;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2202;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2199
                                            in
                                         FStar_All.pipe_right uu____2198
                                           (FStar_TypeChecker_Env.lcomp_of_comp
                                              env1)
                                          in
                                       let e3 =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e2, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____2232 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____2232 with
                                        | (e4,c1,g') ->
                                            let uu____2242 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____2242))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____2261 =
               let uu____2262 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____2262 Prims.fst  in
             FStar_All.pipe_right uu____2261 instantiate_both  in
           ((let uu____2271 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____2271
             then
               let uu____2272 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____2273 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2272
                 uu____2273
             else ());
            (let uu____2275 = tc_term (no_inst env2) head1  in
             match uu____2275 with
             | (head2,chead,g_head) ->
                 let uu____2285 =
                   let uu____2289 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____2289
                   then
                     let uu____2293 = FStar_TypeChecker_Env.expected_typ env0
                        in
                     check_short_circuit_args env2 head2 chead g_head args
                       uu____2293
                   else
                     (let uu____2296 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____2296)
                    in
                 (match uu____2285 with
                  | (e1,c,g) ->
                      ((let uu____2305 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____2305
                        then
                          let uu____2306 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2306
                        else ());
                       (let c1 =
                          let uu____2309 =
                            ((FStar_TypeChecker_Env.should_verify env2) &&
                               (let uu____2310 =
                                  FStar_Syntax_Util.is_lcomp_partial_return c
                                   in
                                Prims.op_Negation uu____2310))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                             in
                          if uu____2309
                          then
                            FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                              env2 e1 c
                          else c  in
                        let uu____2312 = comp_check_expected_typ env0 e1 c1
                           in
                        match uu____2312 with
                        | (e2,c2,g') ->
                            let gimp =
                              let uu____2323 =
                                let uu____2324 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____2324.FStar_Syntax_Syntax.n  in
                              match uu____2323 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2328) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c2.FStar_Syntax_Syntax.lcomp_res_typ),
                                      (head2.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___90_2360 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___90_2360.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___90_2360.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___90_2360.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2385 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____2387 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____2387
                               in
                            ((let uu____2389 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____2389
                              then
                                let uu____2390 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____2391 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2390 uu____2391
                              else ());
                             (e2, c2, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2421 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____2421 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____2433 = tc_term env12 e1  in
                (match uu____2433 with
                 | (e11,c1,g1) ->
                     let uu____2443 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2449 = FStar_Syntax_Util.type_u ()  in
                           (match uu____2449 with
                            | (k,uu____2455) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k  in
                                let uu____2457 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t
                                   in
                                (uu____2457, res_t))
                        in
                     (match uu____2443 with
                      | (env_branches,res_t) ->
                          ((let uu____2464 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____2464
                            then
                              let uu____2465 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2465
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.lcomp_res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____2516 =
                              let uu____2519 =
                                FStar_List.fold_right
                                  (fun uu____2538  ->
                                     fun uu____2539  ->
                                       match (uu____2538, uu____2539) with
                                       | ((uu____2571,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2604 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), uu____2604))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____2519 with
                              | (cases,g) ->
                                  let uu____2625 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____2625, g)
                               in
                            match uu____2516 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind env1 (Some e11)
                                    c1 ((Some guard_x), c_branches)
                                   in
                                let e2 =
                                  let mk_match scrutinee =
                                    let scrutinee1 =
                                      FStar_TypeChecker_Util.maybe_lift env1
                                        scrutinee
                                        c1.FStar_Syntax_Syntax.lcomp_name
                                        cres.FStar_Syntax_Syntax.lcomp_name
                                        c1.FStar_Syntax_Syntax.lcomp_res_typ
                                       in
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____2675  ->
                                              match uu____2675 with
                                              | ((pat,wopt,br),uu____2691,lc,uu____2693)
                                                  ->
                                                  let uu____2700 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.lcomp_name
                                                      cres.FStar_Syntax_Syntax.lcomp_name
                                                      lc.FStar_Syntax_Syntax.lcomp_res_typ
                                                     in
                                                  (pat, wopt, uu____2700)))
                                       in
                                    let e2 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_match
                                            (scrutinee1, branches)))
                                        (Some
                                           ((cres.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    (FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_ascribed
                                          (e2,
                                            (FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.lcomp_res_typ)),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.lcomp_name)))))
                                      None e2.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____2739 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.lcomp_name
                                     in
                                  if uu____2739
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____2746 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____2746  in
                                     let lb =
                                       let uu____2748 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.lcomp_name
                                          in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (FStar_Util.Inl guard_x);
                                         FStar_Syntax_Syntax.lbunivs = [];
                                         FStar_Syntax_Syntax.lbtyp =
                                           (c1.FStar_Syntax_Syntax.lcomp_res_typ);
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____2748;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       }  in
                                     let e2 =
                                       let uu____2752 =
                                         let uu____2755 =
                                           let uu____2756 =
                                             let uu____2764 =
                                               let uu____2765 =
                                                 let uu____2766 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____2766]  in
                                               FStar_Syntax_Subst.close
                                                 uu____2765 e_match
                                                in
                                             ((false, [lb]), uu____2764)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____2756
                                            in
                                         FStar_Syntax_Syntax.mk uu____2755
                                          in
                                       uu____2752
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.lcomp_name
                                       cres.FStar_Syntax_Syntax.lcomp_res_typ)
                                   in
                                ((let uu____2780 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____2780
                                  then
                                    let uu____2781 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____2782 =
                                      let uu____2783 =
                                        cres.FStar_Syntax_Syntax.lcomp_as_comp
                                          ()
                                         in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____2783
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____2781 uu____2782
                                  else ());
                                 (let uu____2785 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e2, cres, uu____2785))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2788;
                FStar_Syntax_Syntax.lbunivs = uu____2789;
                FStar_Syntax_Syntax.lbtyp = uu____2790;
                FStar_Syntax_Syntax.lbeff = uu____2791;
                FStar_Syntax_Syntax.lbdef = uu____2792;_}::[]),uu____2793)
           ->
           ((let uu____2808 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____2808
             then
               let uu____2809 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____2809
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2811),uu____2812) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2822;
                FStar_Syntax_Syntax.lbunivs = uu____2823;
                FStar_Syntax_Syntax.lbtyp = uu____2824;
                FStar_Syntax_Syntax.lbeff = uu____2825;
                FStar_Syntax_Syntax.lbdef = uu____2826;_}::uu____2827),uu____2828)
           ->
           ((let uu____2844 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____2844
             then
               let uu____2845 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____2845
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____2847),uu____2848) ->
           check_inner_let_rec env1 top)

and tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____2892 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____2892 with
        | (e2,t1,implicits,_subst) ->
            let tc =
              let uu____2907 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____2907
              then FStar_Util.Inl t1
              else
                (let uu____2911 =
                   let uu____2912 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_TypeChecker_Env.lcomp_of_comp env1 uu____2912  in
                 FStar_Util.Inr uu____2911)
               in
            let is_data_ctor uu___79_2917 =
              match uu___79_2917 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____2920 -> false  in
            let uu____2922 =
              (is_data_ctor dc) &&
                (let uu____2923 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____2923)
               in
            if uu____2922
            then
              let uu____2929 =
                let uu____2930 =
                  let uu____2933 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  let uu____2936 = FStar_TypeChecker_Env.get_range env1  in
                  (uu____2933, uu____2936)  in
                FStar_Errors.Error uu____2930  in
              Prims.raise uu____2929
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____2947 =
            let uu____2948 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____2948
             in
          failwith uu____2947
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____2967 =
              let uu____2968 = FStar_Syntax_Subst.compress t1  in
              uu____2968.FStar_Syntax_Syntax.n  in
            match uu____2967 with
            | FStar_Syntax_Syntax.Tm_arrow uu____2971 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____2979 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___91_2999 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___91_2999.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___91_2999.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___91_2999.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____3027 =
            let uu____3034 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____3034 with
            | None  ->
                let uu____3042 = FStar_Syntax_Util.type_u ()  in
                (match uu____3042 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard)  in
          (match uu____3027 with
           | (t,uu____3063,g0) ->
               let uu____3071 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____3071 with
                | (e1,uu____3082,g1) ->
                    let uu____3090 =
                      let uu____3091 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____3091
                        (FStar_TypeChecker_Env.lcomp_of_comp env1)
                       in
                    let uu____3092 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____3090, uu____3092)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let t =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then x.FStar_Syntax_Syntax.sort
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          let x1 =
            let uu___92_3101 = x  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___92_3101.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___92_3101.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = t
            }  in
          (FStar_TypeChecker_Common.insert_bv x1 t;
           (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
            let uu____3104 =
              FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
            match uu____3104 with
            | (e2,t1,implicits,_subst) ->
                let tc =
                  let uu____3119 = FStar_TypeChecker_Env.should_verify env1
                     in
                  if uu____3119
                  then FStar_Util.Inl t1
                  else
                    (let uu____3123 =
                       let uu____3124 = FStar_Syntax_Syntax.mk_Total t1  in
                       FStar_All.pipe_left
                         (FStar_TypeChecker_Env.lcomp_of_comp env1)
                         uu____3124
                        in
                     FStar_Util.Inr uu____3123)
                   in
                value_check_expected_typ env1 e2 tc implicits))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3126;
             FStar_Syntax_Syntax.pos = uu____3127;
             FStar_Syntax_Syntax.vars = uu____3128;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____3136 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3136 with
           | (us',t) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3153 =
                     let uu____3154 =
                       let uu____3157 = FStar_TypeChecker_Env.get_range env1
                          in
                       ("Unexpected number of universe instantiations",
                         uu____3157)
                        in
                     FStar_Errors.Error uu____3154  in
                   Prims.raise uu____3153)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____3165 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___93_3167 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___94_3168 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___94_3168.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___94_3168.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___93_3167.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___93_3167.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____3183 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3183 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3195 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3195 with
           | (us,t) ->
               ((let uu____3208 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____3208
                 then
                   let uu____3209 =
                     let uu____3210 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____3210  in
                   let uu____3211 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3212 =
                     let uu____3213 =
                       let uu____3214 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.range_of_lid uu____3214  in
                     FStar_Range.string_of_range uu____3213  in
                   let uu____3215 =
                     let uu____3216 =
                       let uu____3217 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.range_of_lid uu____3217  in
                     FStar_Range.string_of_use_range uu____3216  in
                   let uu____3218 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s"
                     uu____3209 uu____3211 uu____3212 uu____3215 uu____3218
                 else ());
                (let fv' =
                   let uu___95_3221 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___96_3222 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___96_3222.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___96_3222.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___95_3221.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___95_3221.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 FStar_TypeChecker_Common.insert_fv fv t;
                 (let e1 =
                    let uu____3237 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3237 us  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
              (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____3273 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3273 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____3282 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____3282 with
                | (env2,uu____3290) ->
                    let uu____3293 = tc_binders env2 bs1  in
                    (match uu____3293 with
                     | (bs2,env3,g,us) ->
                         let uu____3305 = tc_comp env3 c1  in
                         (match uu____3305 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___97_3318 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___97_3318.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___97_3318.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___97_3318.FStar_Syntax_Syntax.vars)
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
                                  let uu____3337 =
                                    FStar_TypeChecker_Rel.close_guard bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3337
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
          let uu____3372 =
            let uu____3375 =
              let uu____3376 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____3376]  in
            FStar_Syntax_Subst.open_term uu____3375 phi  in
          (match uu____3372 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____3383 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____3383 with
                | (env2,uu____3391) ->
                    let uu____3394 =
                      let uu____3401 = FStar_List.hd x1  in
                      tc_binder env2 uu____3401  in
                    (match uu____3394 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3418 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____3418
                           then
                             let uu____3419 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____3420 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____3421 =
                               FStar_Syntax_Print.bv_to_string (Prims.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3419 uu____3420 uu____3421
                           else ());
                          (let uu____3423 = FStar_Syntax_Util.type_u ()  in
                           match uu____3423 with
                           | (t_phi,uu____3430) ->
                               let uu____3431 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____3431 with
                                | (phi2,uu____3439,f2) ->
                                    let e1 =
                                      let uu___98_3444 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x2) phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___98_3444.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___98_3444.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___98_3444.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____3463 =
                                        FStar_TypeChecker_Rel.close_guard
                                          [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3463
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3472) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____3497 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____3497
            then
              let uu____3498 =
                FStar_Syntax_Print.term_to_string
                  (let uu___99_3499 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___99_3499.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___99_3499.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___99_3499.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3498
            else ());
           (let uu____3518 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____3518 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3526 ->
          let uu____3527 =
            let uu____3528 = FStar_Syntax_Print.term_to_string top  in
            let uu____3529 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3528
              uu____3529
             in
          failwith uu____3527

and tc_constant :
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3535 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3536,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3542,Some uu____3543) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3551 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3555 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3556 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3557 ->
          FStar_TypeChecker_Common.t_range
      | uu____3558 ->
          Prims.raise (FStar_Errors.Error ("Unsupported constant", r))

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
      | FStar_Syntax_Syntax.Total (t,uu____3569) ->
          let uu____3576 = FStar_Syntax_Util.type_u ()  in
          (match uu____3576 with
           | (k,u) ->
               let uu____3584 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3584 with
                | (t1,uu____3592,g) ->
                    let uu____3594 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u)  in
                    (uu____3594, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3596) ->
          let uu____3603 = FStar_Syntax_Util.type_u ()  in
          (match uu____3603 with
           | (k,u) ->
               let uu____3611 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3611 with
                | (t1,uu____3619,g) ->
                    let uu____3621 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u)  in
                    (uu____3621, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.comp_typ_name
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
            (FStar_Syntax_Syntax.mk_Tm_app head2
               c1.FStar_Syntax_Syntax.effect_args) None
              c0.FStar_Syntax_Syntax.pos
             in
          let uu____3641 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____3641 with
           | (tc1,uu____3649,f) ->
               let uu____3651 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____3651 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____3681 =
                        let uu____3682 = FStar_Syntax_Subst.compress head3
                           in
                        uu____3682.FStar_Syntax_Syntax.n  in
                      match uu____3681 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3685,us) -> us
                      | uu____3691 -> []  in
                    let uu____3692 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____3692 with
                     | (uu____3705,args1) ->
                         let uu____3721 =
                           let uu____3726 =
                             FStar_All.pipe_right
                               c1.FStar_Syntax_Syntax.flags
                               (FStar_List.map
                                  (fun uu___80_3736  ->
                                     match uu___80_3736 with
                                     | FStar_Syntax_Syntax.DECREASES e ->
                                         let uu____3742 =
                                           FStar_TypeChecker_Env.clear_expected_typ
                                             env
                                            in
                                         (match uu____3742 with
                                          | (env1,uu____3749) ->
                                              let uu____3752 =
                                                tc_tot_or_gtot_term env1 e
                                                 in
                                              (match uu____3752 with
                                               | (e1,uu____3759,g) ->
                                                   ((FStar_Syntax_Syntax.DECREASES
                                                       e1), g)))
                                     | f1 ->
                                         (f1,
                                           FStar_TypeChecker_Rel.trivial_guard)))
                              in
                           FStar_All.pipe_right uu____3726 FStar_List.unzip
                            in
                         (match uu____3721 with
                          | (flags,guards) ->
                              let c2 =
                                FStar_Syntax_Syntax.mk_Comp
                                  (let uu___100_3779 = c1  in
                                   {
                                     FStar_Syntax_Syntax.comp_typ_name =
                                       (uu___100_3779.FStar_Syntax_Syntax.comp_typ_name);
                                     FStar_Syntax_Syntax.comp_univs =
                                       comp_univs;
                                     FStar_Syntax_Syntax.effect_args = args1;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___100_3779.FStar_Syntax_Syntax.flags)
                                   })
                                 in
                              let u_c =
                                let uu____3781 =
                                  FStar_TypeChecker_Util.effect_repr env c2
                                   in
                                match uu____3781 with
                                | None  ->
                                    let uu____3783 =
                                      let uu____3784 =
                                        let uu____3789 =
                                          FStar_TypeChecker_Env.comp_as_normal_comp_typ
                                            env c2
                                           in
                                        uu____3789.FStar_TypeChecker_Env.nct_result
                                         in
                                      Prims.fst uu____3784  in
                                    env.FStar_TypeChecker_Env.universe_of env
                                      uu____3783
                                | Some tm ->
                                    env.FStar_TypeChecker_Env.universe_of env
                                      tm
                                 in
                              let uu____3793 =
                                FStar_List.fold_left
                                  FStar_TypeChecker_Rel.conj_guard f guards
                                 in
                              (c2, u_c, uu____3793)))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____3801 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3804 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3804
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3807 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3807
        | FStar_Syntax_Syntax.U_name x -> u2  in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____3811 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____3811 Prims.snd
         | uu____3816 -> aux u)

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
            let uu____3837 =
              let uu____3838 =
                let uu____3841 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top
                   in
                (uu____3841, (top.FStar_Syntax_Syntax.pos))  in
              FStar_Errors.Error uu____3838  in
            Prims.raise uu____3837  in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____3895 bs2 bs_expected1 =
              match uu____3895 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             let uu____3992 =
                               let uu____3993 =
                                 let uu____3996 =
                                   let uu____3997 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____3997
                                    in
                                 let uu____3998 =
                                   FStar_Syntax_Syntax.range_of_bv hd1  in
                                 (uu____3996, uu____3998)  in
                               FStar_Errors.Error uu____3993  in
                             Prims.raise uu____3992
                         | uu____3999 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____4003 =
                           let uu____4006 =
                             let uu____4007 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____4007.FStar_Syntax_Syntax.n  in
                           match uu____4006 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4012 ->
                               ((let uu____4014 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____4014
                                 then
                                   let uu____4015 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4015
                                 else ());
                                (let uu____4017 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____4017 with
                                 | (t,uu____4024,g1) ->
                                     let g2 =
                                       let uu____4027 =
                                         FStar_TypeChecker_Env.get_range env2
                                          in
                                       let uu____4028 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t
                                          in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4027
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4028
                                        in
                                     let g3 =
                                       let uu____4030 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4030
                                        in
                                     (t, g3)))
                            in
                         match uu____4003 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___101_4046 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___101_4046.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___101_4046.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____4055 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____4055
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
                  | uu____4151 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4155 = tc_binders env1 bs  in
                  match uu____4155 with
                  | (bs1,envbody,g,uu____4174) ->
                      let uu____4175 =
                        let uu____4180 =
                          let uu____4181 = FStar_Syntax_Subst.compress body1
                             in
                          uu____4181.FStar_Syntax_Syntax.n  in
                        match uu____4180 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,FStar_Util.Inr c,uu____4190) ->
                            let uu____4209 = tc_comp envbody c  in
                            (match uu____4209 with
                             | (c1,uu____4218,g') ->
                                 let uu____4220 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((Some c1), body1, uu____4220))
                        | uu____4222 -> (None, body1, g)  in
                      (match uu____4175 with
                       | (copt,body2,g1) ->
                           (None, bs1, [], copt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____4272 =
                    let uu____4273 = FStar_Syntax_Subst.compress t2  in
                    uu____4273.FStar_Syntax_Syntax.n  in
                  match uu____4272 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4304 -> failwith "Impossible");
                       (let uu____4308 = tc_binders env1 bs  in
                        match uu____4308 with
                        | (bs1,envbody,g,uu____4328) ->
                            let uu____4329 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____4329 with
                             | (envbody1,uu____4346) ->
                                 ((Some (t2, true)), bs1, [], None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4357) ->
                      let uu____4362 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____4362 with
                       | (uu____4387,bs1,bs',copt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, env2, body2,
                             g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4423 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____4423 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____4481 c_expected2 =
                               match uu____4481 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____4530 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____4530)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____4538 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____4538
                                           in
                                        let uu____4539 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____4539)
                                    | Some (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        if FStar_Syntax_Util.is_named_tot c
                                        then
                                          let t3 =
                                            let uu____4555 =
                                              FStar_TypeChecker_Env.result_typ
                                                env3 c
                                               in
                                            unfold_whnf env3 uu____4555  in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____4575 =
                                                 check_binders env3 more_bs
                                                   bs_expected3
                                                  in
                                               (match uu____4575 with
                                                | (env4,bs',more1,guard',subst2)
                                                    ->
                                                    let uu____4602 =
                                                      let uu____4615 =
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          guard guard'
                                                         in
                                                      (env4,
                                                        (FStar_List.append
                                                           bs2 bs'), more1,
                                                        uu____4615, subst2)
                                                       in
                                                    handle_more uu____4602
                                                      c_expected3)
                                           | uu____4624 ->
                                               let uu____4625 =
                                                 let uu____4626 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3
                                                    in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____4626
                                                  in
                                               fail uu____4625 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2)
                                in
                             let uu____4642 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____4642 c_expected1  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___102_4677 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___102_4677.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___102_4677.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___102_4677.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___102_4677.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___102_4677.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___102_4677.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___102_4677.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___102_4677.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___102_4677.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___102_4677.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___102_4677.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___102_4677.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___102_4677.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___102_4677.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___102_4677.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___102_4677.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___102_4677.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___102_4677.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___102_4677.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___102_4677.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___102_4677.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___102_4677.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___102_4677.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____4691  ->
                                     fun uu____4692  ->
                                       match (uu____4691, uu____4692) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____4717 =
                                             let uu____4721 =
                                               let uu____4722 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4722 Prims.fst
                                                in
                                             tc_term uu____4721 t3  in
                                           (match uu____4717 with
                                            | (t4,uu____4734,uu____4735) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____4742 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___103_4743
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___103_4743.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___103_4743.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____4742 ::
                                                        letrec_binders
                                                  | uu____4744 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____4747 =
                             check_actuals_against_formals env1 bs
                               bs_expected1
                              in
                           (match uu____4747 with
                            | (envbody,bs1,g,c) ->
                                let uu____4777 =
                                  let uu____4781 =
                                    FStar_TypeChecker_Env.should_verify env1
                                     in
                                  if uu____4781
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, [])  in
                                (match uu____4777 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       let uu____4804 =
                                         FStar_TypeChecker_Env.result_typ
                                           env1 c
                                          in
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1 uu____4804
                                        in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), envbody2, body1, g))))
                  | uu____4815 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____4828 = unfold_whnf env1 t2  in
                        as_function_typ true uu____4828
                      else
                        (let uu____4830 =
                           expected_function_typ1 env1 None body1  in
                         match uu____4830 with
                         | (uu____4854,bs1,uu____4856,c_opt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, envbody,
                               body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____4877 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____4877 with
          | (env1,topt) ->
              ((let uu____4889 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____4889
                then
                  let uu____4890 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____4890
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____4894 = expected_function_typ1 env1 topt body  in
                match uu____4894 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____4924 =
                      tc_term
                        (let uu___104_4928 = envbody  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___104_4928.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___104_4928.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___104_4928.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___104_4928.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___104_4928.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___104_4928.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___104_4928.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___104_4928.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___104_4928.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___104_4928.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___104_4928.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___104_4928.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___104_4928.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___104_4928.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___104_4928.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___104_4928.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___104_4928.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___104_4928.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___104_4928.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___104_4928.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___104_4928.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___104_4928.FStar_TypeChecker_Env.qname_and_index)
                         }) body1
                       in
                    (match uu____4924 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         ((let uu____4937 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits")
                              in
                           if uu____4937
                           then
                             let uu____4938 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits)
                                in
                             let uu____4947 =
                               let uu____4948 =
                                 cbody.FStar_Syntax_Syntax.lcomp_as_comp ()
                                  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____4948
                                in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____4938 uu____4947
                           else ());
                          (let uu____4950 =
                             let uu____4954 =
                               let uu____4957 =
                                 cbody.FStar_Syntax_Syntax.lcomp_as_comp ()
                                  in
                               (body2, uu____4957)  in
                             check_expected_effect
                               (let uu___105_4962 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___105_4962.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___105_4962.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___105_4962.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___105_4962.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___105_4962.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___105_4962.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___105_4962.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___105_4962.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___105_4962.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___105_4962.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___105_4962.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___105_4962.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___105_4962.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___105_4962.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___105_4962.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___105_4962.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___105_4962.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___105_4962.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___105_4962.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___105_4962.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___105_4962.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___105_4962.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___105_4962.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____4954
                              in
                           match uu____4950 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard
                                  in
                               let guard2 =
                                 let uu____4971 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____4972 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1
                                         in
                                      Prims.op_Negation uu____4972)
                                    in
                                 if uu____4971
                                 then
                                   let uu____4973 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1
                                      in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____4973
                                 else
                                   (let guard2 =
                                      let uu____4976 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1
                                         in
                                      FStar_TypeChecker_Rel.close_guard
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____4976
                                       in
                                    guard2)
                                  in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1  in
                               let e =
                                 let uu____4981 =
                                   let uu____4988 =
                                     let uu____4994 =
                                       FStar_TypeChecker_Env.lcomp_of_comp
                                         env1 (FStar_Util.dflt cbody1 c_opt)
                                        in
                                     FStar_Util.Inl uu____4994  in
                                   Some uu____4988  in
                                 FStar_Syntax_Util.abs bs1 body3 uu____4981
                                  in
                               let uu____5003 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t
                                        in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5018 -> (e, t1, guard2)
                                      | uu____5026 ->
                                          let uu____5027 =
                                            if use_teq
                                            then
                                              let uu____5032 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed
                                                 in
                                              (e, uu____5032)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1
                                             in
                                          (match uu____5027 with
                                           | (e1,guard') ->
                                               let uu____5039 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard'
                                                  in
                                               (e1, t1, uu____5039)))
                                 | None  -> (e, tfun_computed, guard2)  in
                               (match uu____5003 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1
                                       in
                                    let uu____5050 =
                                      let uu____5053 =
                                        FStar_TypeChecker_Env.lcomp_of_comp
                                          env1 c
                                         in
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1 uu____5053 guard3
                                       in
                                    (match uu____5050 with
                                     | (c1,g1) -> (e1, c1, g1))))))))

and check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)
            Prims.list ->
            FStar_Syntax_Syntax.typ Prims.option ->
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
              let thead = chead.FStar_Syntax_Syntax.lcomp_res_typ  in
              (let uu____5087 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____5087
               then
                 let uu____5088 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____5089 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5088
                   uu____5089
               else ());
              (let monadic_application uu____5132 subst1 arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____5132 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.lcomp_res_typ
                        in
                     let cres1 =
                       let uu___106_5174 = cres  in
                       {
                         FStar_Syntax_Syntax.lcomp_name =
                           (uu___106_5174.FStar_Syntax_Syntax.lcomp_name);
                         FStar_Syntax_Syntax.lcomp_univs =
                           (uu___106_5174.FStar_Syntax_Syntax.lcomp_univs);
                         FStar_Syntax_Syntax.lcomp_indices =
                           (uu___106_5174.FStar_Syntax_Syntax.lcomp_indices);
                         FStar_Syntax_Syntax.lcomp_res_typ = rt;
                         FStar_Syntax_Syntax.lcomp_cflags =
                           (uu___106_5174.FStar_Syntax_Syntax.lcomp_cflags);
                         FStar_Syntax_Syntax.lcomp_as_comp =
                           (uu___106_5174.FStar_Syntax_Syntax.lcomp_as_comp)
                       }  in
                     let uu____5175 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_Syntax_Subst.subst_lcomp subst1 cres1  in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard
                              in
                           let refine_with_equality =
                             (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
                               &&
                               (FStar_All.pipe_right arg_comps_rev
                                  (FStar_Util.for_some
                                     (fun uu___81_5202  ->
                                        match uu___81_5202 with
                                        | (uu____5211,uu____5212,FStar_Util.Inl
                                           uu____5213) -> false
                                        | (uu____5224,uu____5225,FStar_Util.Inr
                                           c) ->
                                            let uu____5235 =
                                              FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                c
                                               in
                                            Prims.op_Negation uu____5235)))
                              in
                           let cres3 =
                             if refine_with_equality
                             then
                               let uu____5237 =
                                 (FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets))
                                   (Some
                                      ((cres2.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                   r
                                  in
                               FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                 env uu____5237 cres2
                             else
                               ((let uu____5248 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____5248
                                 then
                                   let uu____5249 =
                                     FStar_Syntax_Print.term_to_string head2
                                      in
                                   let uu____5250 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   let uu____5251 =
                                     FStar_TypeChecker_Rel.guard_to_string
                                       env g
                                      in
                                   FStar_Util.print3
                                     "Not refining result: f=%s; cres=%s; guard=%s\n"
                                     uu____5249 uu____5250 uu____5251
                                 else ());
                                cres2)
                              in
                           (cres3, g)
                       | uu____5253 ->
                           let g =
                             let uu____5258 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard
                                in
                             FStar_All.pipe_right uu____5258
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____5259 =
                             let uu____5260 =
                               let uu____5261 =
                                 let uu____5262 =
                                   let uu____5263 =
                                     cres1.FStar_Syntax_Syntax.lcomp_as_comp
                                       ()
                                      in
                                   FStar_Syntax_Util.arrow bs uu____5263  in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5262
                                  in
                               FStar_Syntax_Syntax.mk_Total uu____5261  in
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.lcomp_of_comp env)
                               uu____5260
                              in
                           (uu____5259, g)
                        in
                     (match uu____5175 with
                      | (cres2,guard1) ->
                          ((let uu____5270 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____5270
                            then
                              let uu____5271 =
                                FStar_Syntax_Print.lcomp_to_string cres2  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5271
                            else ());
                           (let uu____5273 =
                              FStar_List.fold_left
                                (fun uu____5296  ->
                                   fun uu____5297  ->
                                     match (uu____5296, uu____5297) with
                                     | ((args1,out_c,monadic),((e,q),x,c)) ->
                                         (match c with
                                          | FStar_Util.Inl (eff_name,arg_typ)
                                              ->
                                              let uu____5387 =
                                                let uu____5391 =
                                                  let uu____5394 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env e eff_name
                                                      out_c.FStar_Syntax_Syntax.lcomp_name
                                                      arg_typ
                                                     in
                                                  (uu____5394, q)  in
                                                uu____5391 :: args1  in
                                              (uu____5387, out_c, monadic)
                                          | FStar_Util.Inr c1 ->
                                              let monadic1 =
                                                monadic ||
                                                  (let uu____5404 =
                                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                       c1
                                                      in
                                                   Prims.op_Negation
                                                     uu____5404)
                                                 in
                                              let out_c1 =
                                                FStar_TypeChecker_Util.bind
                                                  env None c1 (x, out_c)
                                                 in
                                              let e1 =
                                                FStar_TypeChecker_Util.maybe_monadic
                                                  env e
                                                  c1.FStar_Syntax_Syntax.lcomp_name
                                                  c1.FStar_Syntax_Syntax.lcomp_res_typ
                                                 in
                                              let e2 =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env e1
                                                  c1.FStar_Syntax_Syntax.lcomp_name
                                                  out_c1.FStar_Syntax_Syntax.lcomp_name
                                                  c1.FStar_Syntax_Syntax.lcomp_res_typ
                                                 in
                                              (((e2, q) :: args1), out_c1,
                                                monadic1)))
                                ([], cres2, false) arg_comps_rev
                               in
                            match uu____5273 with
                            | (args1,comp,monadic) ->
                                let comp1 =
                                  FStar_TypeChecker_Util.bind env None chead1
                                    (None, comp)
                                   in
                                let app =
                                  (FStar_Syntax_Syntax.mk_Tm_app head2 args1)
                                    (Some
                                       ((comp1.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                    r
                                   in
                                let app1 =
                                  let uu____5441 =
                                    monadic ||
                                      (let uu____5442 =
                                         FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                           comp1
                                          in
                                       Prims.op_Negation uu____5442)
                                     in
                                  if uu____5441
                                  then
                                    FStar_TypeChecker_Util.maybe_monadic env
                                      app
                                      comp1.FStar_Syntax_Syntax.lcomp_name
                                      comp1.FStar_Syntax_Syntax.lcomp_res_typ
                                  else app  in
                                let uu____5444 =
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    None env app1 comp1 guard1
                                   in
                                (match uu____5444 with
                                 | (comp2,g) -> (app1, comp2, g)))))
                  in
               let rec tc_args head_info uu____5502 bs args1 =
                 match uu____5502 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____5597))::rest,
                         (uu____5599,None )::uu____5600) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t1 = check_no_escape (Some head1) env fvs t  in
                          let uu____5637 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____5637 with
                           | (varg,uu____5648,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1
                                  in
                               let arg =
                                 let uu____5661 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____5661)  in
                               let uu____5662 =
                                 let uu____5684 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst2,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t1))) :: outargs), (arg ::
                                   arg_rets), uu____5684, fvs)
                                  in
                               tc_args head_info uu____5662 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____5775 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___107_5782 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___107_5782.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___107_5782.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____5784 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____5784
                             then
                               let uu____5785 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____5785
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ  in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1
                                in
                             let env2 =
                               let uu___108_5790 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___108_5790.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___108_5790.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___108_5790.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___108_5790.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___108_5790.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___108_5790.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___108_5790.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___108_5790.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___108_5790.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___108_5790.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___108_5790.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___108_5790.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___108_5790.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___108_5790.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___108_5790.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___108_5790.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___108_5790.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___108_5790.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___108_5790.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___108_5790.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___108_5790.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___108_5790.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___108_5790.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             (let uu____5792 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High
                                 in
                              if uu____5792
                              then
                                let uu____5793 =
                                  FStar_Syntax_Print.tag_of_term e  in
                                let uu____5794 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____5795 =
                                  FStar_Syntax_Print.term_to_string targ1  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____5793 uu____5794 uu____5795
                              else ());
                             (let uu____5797 = tc_term env2 e  in
                              match uu____5797 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e1, aq)  in
                                  let uu____5813 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c
                                     in
                                  if uu____5813
                                  then
                                    let subst2 =
                                      let uu____5818 = FStar_List.hd bs  in
                                      maybe_extend_subst subst1 uu____5818 e1
                                       in
                                    tc_args head_info
                                      (subst2,
                                        ((arg, None,
                                           (FStar_Util.Inl
                                              ((c.FStar_Syntax_Syntax.lcomp_name),
                                                (c.FStar_Syntax_Syntax.lcomp_res_typ))))
                                        :: outargs), (arg :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    (let uu____5874 =
                                       FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2
                                         c.FStar_Syntax_Syntax.lcomp_name
                                        in
                                     if uu____5874
                                     then
                                       let subst2 =
                                         let uu____5879 = FStar_List.hd bs
                                            in
                                         maybe_extend_subst subst1 uu____5879
                                           e1
                                          in
                                       tc_args head_info
                                         (subst2,
                                           ((arg, (Some x1),
                                              (FStar_Util.Inr c)) ::
                                           outargs), (arg :: arg_rets), g1,
                                           fvs) rest rest'
                                     else
                                       (let uu____5925 =
                                          let uu____5926 = FStar_List.hd bs
                                             in
                                          FStar_Syntax_Syntax.is_null_binder
                                            uu____5926
                                           in
                                        if uu____5925
                                        then
                                          let newx =
                                            FStar_Syntax_Syntax.new_bv
                                              (Some
                                                 (e1.FStar_Syntax_Syntax.pos))
                                              c.FStar_Syntax_Syntax.lcomp_res_typ
                                             in
                                          let arg' =
                                            let uu____5935 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                newx
                                               in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____5935
                                             in
                                          tc_args head_info
                                            (subst1,
                                              ((arg, (Some newx),
                                                 (FStar_Util.Inr c)) ::
                                              outargs), (arg' :: arg_rets),
                                              g1, fvs) rest rest'
                                        else
                                          (let uu____5973 =
                                             let uu____5995 =
                                               let uu____5997 =
                                                 let uu____5998 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x1
                                                    in
                                                 FStar_Syntax_Syntax.as_arg
                                                   uu____5998
                                                  in
                                               uu____5997 :: arg_rets  in
                                             (subst1,
                                               ((arg, (Some x1),
                                                  (FStar_Util.Inr c)) ::
                                               outargs), uu____5995, g1, (x1
                                               :: fvs))
                                              in
                                           tc_args head_info uu____5973 rest
                                             rest')))))))
                      | (uu____6035,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6056) ->
                          let uu____6086 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____6086 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6109 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____6109
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____6125 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____6125 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____6138 =
                                              FStar_TypeChecker_Env.lcomp_of_comp
                                                env cres'1
                                               in
                                            (head2, chead1, ghead1,
                                              uu____6138)
                                             in
                                          ((let uu____6140 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____6140
                                            then
                                              let uu____6141 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____6141
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____6171 when Prims.op_Negation norm1 ->
                                     let uu____6172 = unfold_whnf env tres1
                                        in
                                     aux true uu____6172
                                 | uu____6173 ->
                                     let uu____6174 =
                                       let uu____6175 =
                                         let uu____6178 =
                                           let uu____6179 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead
                                              in
                                           let uu____6180 =
                                             FStar_Util.string_of_int n_args
                                              in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6179 uu____6180
                                            in
                                         let uu____6184 =
                                           FStar_Syntax_Syntax.argpos arg  in
                                         (uu____6178, uu____6184)  in
                                       FStar_Errors.Error uu____6175  in
                                     Prims.raise uu____6174
                                  in
                               aux false
                                 chead1.FStar_Syntax_Syntax.lcomp_res_typ))
                  in
               let rec check_function_app norm1 tf =
                 let uu____6200 =
                   let uu____6201 = FStar_Syntax_Util.unrefine tf  in
                   uu____6201.FStar_Syntax_Syntax.n  in
                 match uu____6200 with
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
                           let uu____6277 = tc_term env1 e  in
                           (match uu____6277 with
                            | (e1,c,g_e) ->
                                let uu____6290 = tc_args1 env1 tl1  in
                                (match uu____6290 with
                                 | (args2,comps,g_rest) ->
                                     let uu____6312 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____6312)))
                        in
                     let uu____6323 = tc_args1 env args  in
                     (match uu____6323 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____6345 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____6365  ->
                                      match uu____6365 with
                                      | (uu____6373,c) ->
                                          ((c.FStar_Syntax_Syntax.lcomp_res_typ),
                                            None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____6345
                             in
                          let ml_or_tot t r1 =
                            let uu____6385 = FStar_Options.ml_ish ()  in
                            if uu____6385
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____6388 =
                              let uu____6389 =
                                let uu____6390 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____6390 Prims.fst  in
                              FStar_TypeChecker_Util.new_uvar env uu____6389
                               in
                            ml_or_tot uu____6388 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____6397 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____6397
                            then
                              let uu____6398 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____6399 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____6400 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____6398 uu____6399 uu____6400
                            else ());
                           (let uu____6403 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____6403);
                           (let comp =
                              let uu____6405 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.lcomp_of_comp env)
                                  cres
                                 in
                              FStar_List.fold_right
                                (fun uu____6408  ->
                                   fun out  ->
                                     match uu____6408 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind env None
                                           c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____6405
                               in
                            let uu____6417 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                r
                               in
                            let uu____6424 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____6417, comp, uu____6424))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____6439 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____6439 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____6454 =
                              FStar_TypeChecker_Env.lcomp_of_comp env c1  in
                            (head1, chead, ghead, uu____6454)  in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | uu____6483 ->
                     if Prims.op_Negation norm1
                     then
                       let uu____6489 = unfold_whnf env tf  in
                       check_function_app true uu____6489
                     else
                       (let uu____6491 =
                          let uu____6492 =
                            let uu____6495 =
                              FStar_TypeChecker_Err.expected_function_typ env
                                tf
                               in
                            (uu____6495, (head1.FStar_Syntax_Syntax.pos))  in
                          FStar_Errors.Error uu____6492  in
                        Prims.raise uu____6491)
                  in
               let uu____6501 =
                 let uu____6502 = FStar_Syntax_Util.unrefine thead  in
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.WHNF] env uu____6502
                  in
               check_function_app false uu____6501)

and check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)
            Prims.list ->
            FStar_Syntax_Syntax.typ Prims.option ->
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
                FStar_Syntax_Subst.compress
                  chead.FStar_Syntax_Syntax.lcomp_res_typ
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_TypeChecker_Env.result_typ env c  in
                  let uu____6546 =
                    FStar_List.fold_left2
                      (fun uu____6559  ->
                         fun uu____6560  ->
                           fun uu____6561  ->
                             match (uu____6559, uu____6560, uu____6561) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____6605 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____6605 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____6617 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____6617 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____6619 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____6619) &&
                                              (let uu____6620 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.lcomp_name
                                                  in
                                               Prims.op_Negation uu____6620))
                                          in
                                       let uu____6621 =
                                         let uu____6627 =
                                           let uu____6633 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____6633]  in
                                         FStar_List.append seen uu____6627
                                          in
                                       let uu____6638 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____6621, uu____6638, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____6546 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____6667 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____6667
                             (FStar_TypeChecker_Env.lcomp_of_comp env)
                         else FStar_TypeChecker_Env.lcomp_of_comp env c  in
                       let uu____6669 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard
                          in
                       (match uu____6669 with | (c2,g) -> (e, c2, g)))
              | uu____6681 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.withinfo_t *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) ->
        ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option *
          FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term *
          FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t)
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____6703 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____6703 with
        | (pattern,when_clause,branch_exp) ->
            let uu____6729 = branch1  in
            (match uu____6729 with
             | (cpat,uu____6749,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____6791 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0
                      in
                   match uu____6791 with
                   | (pat_bvs1,exps,p) ->
                       ((let uu____6813 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____6813
                         then
                           let uu____6814 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____6815 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____6814 uu____6815
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____6818 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____6818 with
                         | (env1,uu____6831) ->
                             let env11 =
                               let uu___109_6835 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___109_6835.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___109_6835.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___109_6835.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___109_6835.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___109_6835.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___109_6835.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___109_6835.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___109_6835.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___109_6835.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___109_6835.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___109_6835.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___109_6835.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___109_6835.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___109_6835.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___109_6835.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___109_6835.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___109_6835.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___109_6835.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___109_6835.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___109_6835.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___109_6835.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___109_6835.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___109_6835.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             let uu____6837 =
                               let uu____6842 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____6854 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High
                                             in
                                          if uu____6854
                                          then
                                            let uu____6855 =
                                              FStar_Syntax_Print.term_to_string
                                                e
                                               in
                                            let uu____6856 =
                                              FStar_Syntax_Print.term_to_string
                                                pat_t
                                               in
                                            FStar_Util.print2
                                              "Checking pattern expression %s against expected type %s\n"
                                              uu____6855 uu____6856
                                          else ());
                                         (let uu____6858 = tc_term env11 e
                                             in
                                          match uu____6858 with
                                          | (e1,lc,g) ->
                                              ((let uu____6868 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High
                                                   in
                                                if uu____6868
                                                then
                                                  let uu____6869 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env e1
                                                     in
                                                  let uu____6870 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env
                                                      lc.FStar_Syntax_Syntax.lcomp_res_typ
                                                     in
                                                  FStar_Util.print2
                                                    "Pre-checked pattern expression %s at type %s\n"
                                                    uu____6869 uu____6870
                                                else ());
                                               (let g' =
                                                  FStar_TypeChecker_Rel.teq
                                                    env
                                                    lc.FStar_Syntax_Syntax.lcomp_res_typ
                                                    expected_pat_t
                                                   in
                                                let g1 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g'
                                                   in
                                                let uu____6874 =
                                                  let uu____6875 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___110_6876 = g1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___110_6876.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___110_6876.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___110_6876.FStar_TypeChecker_Env.implicits)
                                                       })
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____6875
                                                    FStar_TypeChecker_Rel.resolve_implicits
                                                   in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e1
                                                   in
                                                let uvars_to_string uvs =
                                                  let uu____6890 =
                                                    let uu____6892 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____6892
                                                      (FStar_List.map
                                                         (fun uu____6916  ->
                                                            match uu____6916
                                                            with
                                                            | (u,uu____6921)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u))
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____6890
                                                    (FStar_String.concat ", ")
                                                   in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e'
                                                   in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t
                                                   in
                                                (let uu____6934 =
                                                   let uu____6935 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2
                                                      in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation
                                                     uu____6935
                                                    in
                                                 if uu____6934
                                                 then
                                                   let unresolved =
                                                     let uu____6942 =
                                                       FStar_Util.set_difference
                                                         uvs1 uvs2
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____6942
                                                       FStar_Util.set_elements
                                                      in
                                                   let uu____6956 =
                                                     let uu____6957 =
                                                       let uu____6960 =
                                                         let uu____6961 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env e'
                                                            in
                                                         let uu____6962 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env
                                                             expected_pat_t
                                                            in
                                                         let uu____6963 =
                                                           let uu____6964 =
                                                             FStar_All.pipe_right
                                                               unresolved
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____6976
                                                                     ->
                                                                    match uu____6976
                                                                    with
                                                                    | 
                                                                    (u,uu____6984)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____6964
                                                             (FStar_String.concat
                                                                ", ")
                                                            in
                                                         FStar_Util.format3
                                                           "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                           uu____6961
                                                           uu____6962
                                                           uu____6963
                                                          in
                                                       (uu____6960,
                                                         (p.FStar_Syntax_Syntax.p))
                                                        in
                                                     FStar_Errors.Error
                                                       uu____6957
                                                      in
                                                   Prims.raise uu____6956
                                                 else ());
                                                (let uu____6999 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High
                                                    in
                                                 if uu____6999
                                                 then
                                                   let uu____7000 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env e1
                                                      in
                                                   FStar_Util.print1
                                                     "Done checking pattern expression %s\n"
                                                     uu____7000
                                                 else ());
                                                (e1, e'))))))
                                  in
                               FStar_All.pipe_right uu____6842
                                 FStar_List.unzip
                                in
                             (match uu____6837 with
                              | (exps1,norm_exps) ->
                                  let p1 =
                                    FStar_TypeChecker_Util.decorate_pattern
                                      env p exps1
                                     in
                                  (p1, pat_bvs1, pat_env, exps1, norm_exps))))
                    in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____7031 =
                   let uu____7035 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____7035
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____7031 with
                  | (scrutinee_env,uu____7048) ->
                      let uu____7051 = tc_pat true pat_t pattern  in
                      (match uu____7051 with
                       | (pattern1,pat_bvs1,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____7079 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____7094 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____7094
                                 then
                                   Prims.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____7102 =
                                      let uu____7106 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool
                                         in
                                      tc_term uu____7106 e  in
                                    match uu____7102 with
                                    | (e1,c,g) -> ((Some e1), g))
                              in
                           (match uu____7079 with
                            | (when_clause1,g_when) ->
                                let uu____7126 = tc_term pat_env branch_exp
                                   in
                                (match uu____7126 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____7145 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_29  -> Some _0_29)
                                             uu____7145
                                        in
                                     let uu____7147 =
                                       let eqs =
                                         let uu____7153 =
                                           let uu____7154 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____7154  in
                                         if uu____7153
                                         then None
                                         else
                                           FStar_All.pipe_right disj_exps
                                             (FStar_List.fold_left
                                                (fun fopt  ->
                                                   fun e  ->
                                                     let e1 =
                                                       FStar_Syntax_Subst.compress
                                                         e
                                                        in
                                                     match e1.FStar_Syntax_Syntax.n
                                                     with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                       _
                                                       |FStar_Syntax_Syntax.Tm_constant
                                                        _
                                                        |FStar_Syntax_Syntax.Tm_fvar
                                                        _ -> fopt
                                                     | uu____7168 ->
                                                         let clause =
                                                           let uu____7170 =
                                                             env.FStar_TypeChecker_Env.universe_of
                                                               env pat_t
                                                              in
                                                           FStar_Syntax_Util.mk_eq2
                                                             uu____7170 pat_t
                                                             scrutinee_tm e1
                                                            in
                                                         (match fopt with
                                                          | None  ->
                                                              Some clause
                                                          | Some f ->
                                                              let uu____7173
                                                                =
                                                                FStar_Syntax_Util.mk_disj
                                                                  clause f
                                                                 in
                                                              FStar_All.pipe_left
                                                                (fun _0_30 
                                                                   ->
                                                                   Some _0_30)
                                                                uu____7173))
                                                None)
                                          in
                                       let uu____7183 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch
                                          in
                                       match uu____7183 with
                                       | (c1,g_branch1) ->
                                           let uu____7193 =
                                             match (eqs, when_condition) with
                                             | uu____7200 when
                                                 let uu____7205 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation uu____7205
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
                                                 let uu____7213 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____7214 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____7213, uu____7214)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____7221 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____7221
                                                    in
                                                 let uu____7222 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____7223 =
                                                   let uu____7224 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____7224 g_when
                                                    in
                                                 (uu____7222, uu____7223)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let uu____7230 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____7230, g_when)
                                              in
                                           (match uu____7193 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let uu____7238 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs1 c_weak
                                                   in
                                                let uu____7239 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    binders g_when_weak
                                                   in
                                                (uu____7238, uu____7239,
                                                  g_branch1))
                                        in
                                     (match uu____7147 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____7252 =
                                              let uu____7253 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____7253
                                               in
                                            if uu____7252
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____7284 =
                                                     let uu____7285 =
                                                       let uu____7286 =
                                                         let uu____7288 =
                                                           let uu____7292 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____7292
                                                            in
                                                         Prims.snd uu____7288
                                                          in
                                                       FStar_List.length
                                                         uu____7286
                                                        in
                                                     uu____7285 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____7284
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____7301 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____7301 with
                                                     | None  -> []
                                                     | uu____7308 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None
                                                            in
                                                         let disc1 =
                                                           let uu____7316 =
                                                             let uu____7317 =
                                                               let uu____7318
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____7318]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____7317
                                                              in
                                                           uu____7316 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____7323 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool
                                                            in
                                                         [uu____7323]
                                                   else []  in
                                                 let fail uu____7331 =
                                                   let uu____7332 =
                                                     let uu____7333 =
                                                       FStar_Range.string_of_range
                                                         pat_exp.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____7334 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp
                                                        in
                                                     let uu____7335 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____7333 uu____7334
                                                       uu____7335
                                                      in
                                                   failwith uu____7332  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____7356) ->
                                                       head_constructor t1
                                                   | uu____7362 -> fail ()
                                                    in
                                                 let pat_exp1 =
                                                   let uu____7365 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7365
                                                     FStar_Syntax_Util.unmeta
                                                    in
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
                                                     let uu____7382 =
                                                       let uu____7383 =
                                                         tc_constant
                                                           pat_exp1.FStar_Syntax_Syntax.pos
                                                           c2
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____7383
                                                         scrutinee_tm1
                                                         pat_exp1
                                                        in
                                                     [uu____7382]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                   _
                                                   |FStar_Syntax_Syntax.Tm_fvar
                                                   _ ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp1
                                                        in
                                                     let uu____7391 =
                                                       let uu____7392 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____7392
                                                        in
                                                     if uu____7391
                                                     then []
                                                     else
                                                       (let uu____7399 =
                                                          head_constructor
                                                            pat_exp1
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____7399)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____7426 =
                                                       let uu____7427 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____7427
                                                        in
                                                     if uu____7426
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____7436 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____7452
                                                                     ->
                                                                    match uu____7452
                                                                    with
                                                                    | 
                                                                    (ei,uu____7459)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____7469
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____7469
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____7476
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____7483
                                                                    =
                                                                    let uu____7484
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None  in
                                                                    let uu____7489
                                                                    =
                                                                    let uu____7490
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____7490]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____7484
                                                                    uu____7489
                                                                     in
                                                                    uu____7483
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7436
                                                            FStar_List.flatten
                                                           in
                                                        let uu____7502 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____7502
                                                          sub_term_guards)
                                                 | uu____7506 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____7518 =
                                                   let uu____7519 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____7519
                                                    in
                                                 if uu____7518
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____7522 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____7522
                                                       in
                                                    let uu____7525 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____7525 with
                                                    | (k,uu____7529) ->
                                                        let uu____7530 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____7530
                                                         with
                                                         | (t1,uu____7535,uu____7536)
                                                             -> t1))
                                                  in
                                               let branch_guard =
                                                 let uu____7538 =
                                                   FStar_All.pipe_right
                                                     norm_disj_exps
                                                     (FStar_List.map
                                                        (build_and_check_branch_guard
                                                           scrutinee_tm))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____7538
                                                   FStar_Syntax_Util.mk_disj_l
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
                                          ((let uu____7549 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____7549
                                            then
                                              let uu____7550 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____7550
                                            else ());
                                           (let uu____7552 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            (uu____7552, branch_guard, c1,
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
          let uu____7570 = check_let_bound_def true env1 lb  in
          (match uu____7570 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____7584 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then (g1, e1, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____7595 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____7595
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____7597 =
                      let uu____7602 =
                        let uu____7608 =
                          let uu____7613 =
                            let uu____7621 =
                              c1.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____7621)
                             in
                          [uu____7613]  in
                        FStar_TypeChecker_Util.generalize env1 uu____7608  in
                      FStar_List.hd uu____7602  in
                    match uu____7597 with
                    | (uu____7650,univs1,e11,c11) ->
                        let uu____7654 =
                          FStar_TypeChecker_Env.lcomp_of_comp env1 c11  in
                        (g11, e11, univs1, uu____7654))
                  in
               (match uu____7584 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____7662 =
                      let uu____7667 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____7667
                      then
                        let uu____7672 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____7672 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____7689 =
                                   FStar_Options.warn_top_level_effects ()
                                    in
                                 if uu____7689
                                 then
                                   let uu____7690 =
                                     FStar_TypeChecker_Env.get_range env1  in
                                   FStar_Errors.warn uu____7690
                                     FStar_TypeChecker_Err.top_level_effect
                                 else ());
                                (let uu____7692 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____7692, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____7710 =
                              c11.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                            FStar_All.pipe_right uu____7710
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1)
                             in
                          let e21 =
                            let uu____7718 = FStar_Syntax_Util.is_pure_comp c
                               in
                            if uu____7718
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
                    (match uu____7662 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_TypeChecker_Common.t_unit
                            in
                         let cres1 =
                           let uu____7745 =
                             FStar_Syntax_Util.ml_comp
                               FStar_TypeChecker_Common.t_unit
                               e.FStar_Syntax_Syntax.pos
                              in
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.lcomp_of_comp env1)
                             uu____7745
                            in
                         (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                            (Some
                               (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                          (let lb1 =
                             let uu____7751 =
                               FStar_TypeChecker_Env.result_typ env1 c12  in
                             FStar_Syntax_Util.close_univs_and_mk_letbinding
                               None lb.FStar_Syntax_Syntax.lbname univ_vars2
                               uu____7751
                               (FStar_Syntax_Util.comp_effect_name c12) e11
                              in
                           let uu____7753 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos
                              in
                           (uu____7753, cres1,
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____7772 -> failwith "Impossible"

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
            let uu___111_7793 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___111_7793.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___111_7793.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___111_7793.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___111_7793.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___111_7793.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___111_7793.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___111_7793.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___111_7793.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___111_7793.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___111_7793.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___111_7793.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___111_7793.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___111_7793.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___111_7793.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___111_7793.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___111_7793.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___111_7793.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___111_7793.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___111_7793.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___111_7793.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___111_7793.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___111_7793.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___111_7793.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____7794 =
            let uu____7800 =
              let uu____7801 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____7801 Prims.fst  in
            check_let_bound_def false uu____7800 lb  in
          (match uu____7794 with
           | (e1,uu____7813,c1,g1,annotated) ->
               let x =
                 let uu___112_7818 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___112_7818.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___112_7818.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.lcomp_res_typ)
                 }  in
               let uu____7819 =
                 let uu____7822 =
                   let uu____7823 = FStar_Syntax_Syntax.mk_binder x  in
                   [uu____7823]  in
                 FStar_Syntax_Subst.open_term uu____7822 e2  in
               (match uu____7819 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb  in
                    let x1 = Prims.fst xbinder  in
                    let uu____7835 =
                      let uu____7839 = FStar_TypeChecker_Env.push_bv env2 x1
                         in
                      tc_term uu____7839 e21  in
                    (match uu____7835 with
                     | (e22,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.bind env2 (Some e1) c1
                             ((Some x1), c2)
                            in
                         let e11 =
                           FStar_TypeChecker_Util.maybe_lift env2 e1
                             c1.FStar_Syntax_Syntax.lcomp_name
                             cres.FStar_Syntax_Syntax.lcomp_name
                             c1.FStar_Syntax_Syntax.lcomp_res_typ
                            in
                         let e23 =
                           FStar_TypeChecker_Util.maybe_lift env2 e22
                             c2.FStar_Syntax_Syntax.lcomp_name
                             cres.FStar_Syntax_Syntax.lcomp_name
                             c2.FStar_Syntax_Syntax.lcomp_res_typ
                            in
                         let lb1 =
                           FStar_Syntax_Util.mk_letbinding
                             (FStar_Util.Inl x1) []
                             c1.FStar_Syntax_Syntax.lcomp_res_typ
                             c1.FStar_Syntax_Syntax.lcomp_name e11
                            in
                         let e3 =
                           let uu____7854 =
                             let uu____7857 =
                               let uu____7858 =
                                 let uu____7866 =
                                   FStar_Syntax_Subst.close xb e23  in
                                 ((false, [lb1]), uu____7866)  in
                               FStar_Syntax_Syntax.Tm_let uu____7858  in
                             FStar_Syntax_Syntax.mk uu____7857  in
                           uu____7854
                             (Some
                                ((cres.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos
                            in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.lcomp_name
                             cres.FStar_Syntax_Syntax.lcomp_res_typ
                            in
                         let x_eq_e1 =
                           let uu____7881 =
                             let uu____7882 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.lcomp_res_typ
                                in
                             let uu____7883 =
                               FStar_Syntax_Syntax.bv_to_name x1  in
                             FStar_Syntax_Util.mk_eq2 uu____7882
                               c1.FStar_Syntax_Syntax.lcomp_res_typ
                               uu____7883 e11
                              in
                           FStar_All.pipe_left
                             (fun _0_31  ->
                                FStar_TypeChecker_Common.NonTrivial _0_31)
                             uu____7881
                            in
                         let g21 =
                           let uu____7885 =
                             let uu____7886 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard uu____7886 g2
                              in
                           FStar_TypeChecker_Rel.close_guard xb uu____7885
                            in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                            in
                         let uu____7888 =
                           let uu____7889 =
                             FStar_TypeChecker_Env.expected_typ env2  in
                           FStar_Option.isSome uu____7889  in
                         if uu____7888
                         then
                           let tt =
                             let uu____7895 =
                               FStar_TypeChecker_Env.expected_typ env2  in
                             FStar_All.pipe_right uu____7895 FStar_Option.get
                              in
                           ((let uu____7899 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____7899
                             then
                               let uu____7900 =
                                 FStar_Syntax_Print.term_to_string tt  in
                               let uu____7901 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.lcomp_res_typ
                                  in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.lcomp_res_typ=%s\n"
                                 uu____7900 uu____7901
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.lcomp_res_typ
                               in
                            (let uu____7906 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____7906
                             then
                               let uu____7907 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.lcomp_res_typ
                                  in
                               let uu____7908 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____7907 uu____7908
                             else ());
                            (e4,
                              ((let uu___113_7910 = cres  in
                                {
                                  FStar_Syntax_Syntax.lcomp_name =
                                    (uu___113_7910.FStar_Syntax_Syntax.lcomp_name);
                                  FStar_Syntax_Syntax.lcomp_univs =
                                    (uu___113_7910.FStar_Syntax_Syntax.lcomp_univs);
                                  FStar_Syntax_Syntax.lcomp_indices =
                                    (uu___113_7910.FStar_Syntax_Syntax.lcomp_indices);
                                  FStar_Syntax_Syntax.lcomp_res_typ = t;
                                  FStar_Syntax_Syntax.lcomp_cflags =
                                    (uu___113_7910.FStar_Syntax_Syntax.lcomp_cflags);
                                  FStar_Syntax_Syntax.lcomp_as_comp =
                                    (uu___113_7910.FStar_Syntax_Syntax.lcomp_as_comp)
                                })), guard)))))
      | uu____7911 -> failwith "Impossible"

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
          let uu____7932 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____7932 with
           | (lbs1,e21) ->
               let uu____7943 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____7943 with
                | (env0,topt) ->
                    let uu____7954 = build_let_rec_env true env0 lbs1  in
                    (match uu____7954 with
                     | (lbs2,rec_env) ->
                         let uu____7965 = check_let_recs rec_env lbs2  in
                         (match uu____7965 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____7977 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____7977
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____7981 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____7981
                                  (fun _0_32  -> Some _0_32)
                                 in
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
                                     let uu____8005 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____8027 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____8027)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8005
                                      in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____8045  ->
                                           match uu____8045 with
                                           | (x,uvs,e,c) ->
                                               let uu____8063 =
                                                 FStar_TypeChecker_Env.result_typ
                                                   env1 c
                                                  in
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 uu____8063
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e)))
                                 in
                              let cres =
                                let uu____8065 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit
                                   in
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.lcomp_of_comp env1)
                                  uu____8065
                                 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____8070 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21
                                   in
                                match uu____8070 with
                                | (lbs5,e22) ->
                                    let uu____8081 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____8096 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env1 g_lbs1
                                       in
                                    (uu____8081, cres, uu____8096)))))))
      | uu____8099 -> failwith "Impossible"

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
          let uu____8120 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____8120 with
           | (lbs1,e21) ->
               let uu____8131 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8131 with
                | (env0,topt) ->
                    let uu____8142 = build_let_rec_env false env0 lbs1  in
                    (match uu____8142 with
                     | (lbs2,rec_env) ->
                         let uu____8153 = check_let_recs rec_env lbs2  in
                         (match uu____8153 with
                          | (lbs3,g_lbs) ->
                              let uu____8164 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___114_8175 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___114_8175.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___114_8175.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___115_8177 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___115_8177.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___115_8177.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___115_8177.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___115_8177.FStar_Syntax_Syntax.lbdef)
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
                              (match uu____8164 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____8194 = tc_term env2 e21  in
                                   (match uu____8194 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs g2
                                           in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_comp
                                            env2 bvs cres
                                           in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.lcomp_res_typ
                                           in
                                        let cres2 =
                                          let uu___116_8208 = cres1  in
                                          {
                                            FStar_Syntax_Syntax.lcomp_name =
                                              (uu___116_8208.FStar_Syntax_Syntax.lcomp_name);
                                            FStar_Syntax_Syntax.lcomp_univs =
                                              (uu___116_8208.FStar_Syntax_Syntax.lcomp_univs);
                                            FStar_Syntax_Syntax.lcomp_indices
                                              =
                                              (uu___116_8208.FStar_Syntax_Syntax.lcomp_indices);
                                            FStar_Syntax_Syntax.lcomp_res_typ
                                              = tres;
                                            FStar_Syntax_Syntax.lcomp_cflags
                                              =
                                              (uu___116_8208.FStar_Syntax_Syntax.lcomp_cflags);
                                            FStar_Syntax_Syntax.lcomp_as_comp
                                              =
                                              (uu___116_8208.FStar_Syntax_Syntax.lcomp_as_comp)
                                          }  in
                                        let uu____8209 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____8209 with
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
                                              | Some uu____8238 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres
                                                     in
                                                  let cres3 =
                                                    let uu___117_8243 = cres2
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.lcomp_name
                                                        =
                                                        (uu___117_8243.FStar_Syntax_Syntax.lcomp_name);
                                                      FStar_Syntax_Syntax.lcomp_univs
                                                        =
                                                        (uu___117_8243.FStar_Syntax_Syntax.lcomp_univs);
                                                      FStar_Syntax_Syntax.lcomp_indices
                                                        =
                                                        (uu___117_8243.FStar_Syntax_Syntax.lcomp_indices);
                                                      FStar_Syntax_Syntax.lcomp_res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.lcomp_cflags
                                                        =
                                                        (uu___117_8243.FStar_Syntax_Syntax.lcomp_cflags);
                                                      FStar_Syntax_Syntax.lcomp_as_comp
                                                        =
                                                        (uu___117_8243.FStar_Syntax_Syntax.lcomp_as_comp)
                                                    }  in
                                                  (e, cres3, guard)))))))))
      | uu____8246 -> failwith "Impossible"

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
        let termination_check_enabled t =
          let uu____8262 = FStar_Syntax_Util.arrow_formals_comp t  in
          match uu____8262 with
          | (uu____8268,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c)
                 in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)
           in
        let uu____8279 =
          FStar_List.fold_left
            (fun uu____8286  ->
               fun lb  ->
                 match uu____8286 with
                 | (lbs1,env1) ->
                     let uu____8298 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____8298 with
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
                              (let uu____8312 =
                                 let uu____8316 =
                                   let uu____8317 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left Prims.fst uu____8317
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___118_8322 = env0  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___118_8322.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___118_8322.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___118_8322.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___118_8322.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___118_8322.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___118_8322.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___118_8322.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___118_8322.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___118_8322.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___118_8322.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___118_8322.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___118_8322.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___118_8322.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___118_8322.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___118_8322.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___118_8322.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___118_8322.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___118_8322.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___118_8322.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___118_8322.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___118_8322.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___118_8322.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___118_8322.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____8316
                                  in
                               match uu____8312 with
                               | (t1,uu____8324,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let uu____8328 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left Prims.ignore
                                       uu____8328);
                                    norm env0 t1))
                             in
                          let env3 =
                            let uu____8330 =
                              (termination_check_enabled t1) &&
                                (FStar_TypeChecker_Env.should_verify env2)
                               in
                            if uu____8330
                            then
                              let uu___119_8331 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___119_8331.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___119_8331.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___119_8331.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___119_8331.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___119_8331.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___119_8331.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___119_8331.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___119_8331.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___119_8331.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___119_8331.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___119_8331.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___119_8331.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___119_8331.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___119_8331.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___119_8331.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___119_8331.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___119_8331.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___119_8331.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___119_8331.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___119_8331.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___119_8331.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___119_8331.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___119_8331.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1)
                             in
                          let lb1 =
                            let uu___120_8341 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_8341.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_8341.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____8279 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____8355 =
        let uu____8360 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____8371 =
                    let uu____8375 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    tc_tot_or_gtot_term uu____8375
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____8371 with
                  | (e,c,g) ->
                      ((let uu____8382 =
                          let uu____8383 = FStar_Syntax_Util.is_total_lcomp c
                             in
                          Prims.op_Negation uu____8383  in
                        if uu____8382
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
                            FStar_Syntax_Const.effect_Tot_lid e
                           in
                        (lb1, g)))))
           in
        FStar_All.pipe_right uu____8360 FStar_List.unzip  in
      match uu____8355 with
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
        let uu____8412 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____8412 with
        | (env1,uu____8422) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____8428 = check_lbtyp top_level env lb  in
            (match uu____8428 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____8454 =
                     tc_maybe_toplevel_term
                       (let uu___121_8458 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___121_8458.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___121_8458.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___121_8458.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___121_8458.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___121_8458.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___121_8458.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___121_8458.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___121_8458.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___121_8458.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___121_8458.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___121_8458.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___121_8458.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___121_8458.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___121_8458.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___121_8458.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___121_8458.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___121_8458.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___121_8458.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___121_8458.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___121_8458.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___121_8458.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___121_8458.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___121_8458.FStar_TypeChecker_Env.qname_and_index)
                        }) e11
                      in
                   match uu____8454 with
                   | (e12,c1,g1) ->
                       let uu____8467 =
                         let uu____8470 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____8473  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____8470 e12 c1 wf_annot
                          in
                       (match uu____8467 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____8483 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____8483
                              then
                                let uu____8484 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____8485 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.lcomp_res_typ
                                   in
                                let uu____8486 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____8484 uu____8485 uu____8486
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))

and check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t
          * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.subst_elt
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
        | uu____8512 ->
            let uu____8513 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____8513 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____8540 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____8540)
                 else
                   (let uu____8545 = FStar_Syntax_Util.type_u ()  in
                    match uu____8545 with
                    | (k,uu____8556) ->
                        let uu____8557 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____8557 with
                         | (t2,uu____8569,g) ->
                             ((let uu____8572 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____8572
                               then
                                 let uu____8573 =
                                   let uu____8574 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____8574  in
                                 let uu____8575 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____8573 uu____8575
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____8578 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____8578))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____8583  ->
      match uu____8583 with
      | (x,imp) ->
          let uu____8594 = FStar_Syntax_Util.type_u ()  in
          (match uu____8594 with
           | (tu,u) ->
               ((let uu____8606 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____8606
                 then
                   let uu____8607 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____8608 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____8609 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____8607 uu____8608 uu____8609
                 else ());
                (let uu____8611 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____8611 with
                 | (t,uu____8622,g) ->
                     let x1 =
                       ((let uu___122_8627 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___122_8627.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___122_8627.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____8629 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____8629
                       then
                         let uu____8630 =
                           FStar_Syntax_Print.bv_to_string (Prims.fst x1)  in
                         let uu____8631 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____8630 uu____8631
                       else ());
                      (let uu____8633 = push_binding env x1  in
                       (x1, uu____8633, g, u))))))

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
            let uu____8684 = tc_binder env1 b  in
            (match uu____8684 with
             | (b1,env',g,u) ->
                 let uu____8707 = aux env' bs2  in
                 (match uu____8707 with
                  | (bs3,env'1,g',us) ->
                      let uu____8736 =
                        let uu____8737 =
                          FStar_TypeChecker_Rel.close_guard [b1] g'  in
                        FStar_TypeChecker_Rel.conj_guard g uu____8737  in
                      ((b1 :: bs3), env'1, uu____8736, (u :: us))))
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
          (fun uu____8780  ->
             fun uu____8781  ->
               match (uu____8780, uu____8781) with
               | ((t,imp),(args1,g)) ->
                   let uu____8818 = tc_term env1 t  in
                   (match uu____8818 with
                    | (t1,uu____8828,g') ->
                        let uu____8830 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____8830))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____8848  ->
             match uu____8848 with
             | (pats1,g) ->
                 let uu____8862 = tc_args env p  in
                 (match uu____8862 with
                  | (args,g') ->
                      let uu____8870 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____8870))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____8878 = tc_maybe_toplevel_term env e  in
      match uu____8878 with
      | (e1,c,g) ->
          let uu____8888 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____8888
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = c.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             let c2 = norm_c env c1  in
             let uu____8898 =
               let uu____8901 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____8901
               then
                 let uu____8904 =
                   let uu____8905 = FStar_TypeChecker_Env.result_typ env c2
                      in
                   FStar_Syntax_Syntax.mk_Total uu____8905  in
                 (uu____8904, false)
               else
                 (let uu____8907 =
                    let uu____8908 = FStar_TypeChecker_Env.result_typ env c2
                       in
                    FStar_Syntax_Syntax.mk_GTotal uu____8908  in
                  (uu____8907, true))
                in
             match uu____8898 with
             | (target_comp,allow_ghost) ->
                 let uu____8914 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____8914 with
                  | Some g' ->
                      let uu____8920 =
                        FStar_TypeChecker_Env.lcomp_of_comp env target_comp
                         in
                      let uu____8921 = FStar_TypeChecker_Rel.conj_guard g1 g'
                         in
                      (e1, uu____8920, uu____8921)
                  | uu____8922 ->
                      if allow_ghost
                      then
                        let uu____8927 =
                          let uu____8928 =
                            let uu____8931 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2
                               in
                            (uu____8931, (e1.FStar_Syntax_Syntax.pos))  in
                          FStar_Errors.Error uu____8928  in
                        Prims.raise uu____8927
                      else
                        (let uu____8936 =
                           let uu____8937 =
                             let uu____8940 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2
                                in
                             (uu____8940, (e1.FStar_Syntax_Syntax.pos))  in
                           FStar_Errors.Error uu____8937  in
                         Prims.raise uu____8936)))

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
      let uu____8953 = tc_tot_or_gtot_term env t  in
      match uu____8953 with
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
      (let uu____8973 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____8973
       then
         let uu____8974 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____8974
       else ());
      (let env1 =
         let uu___123_8977 = env  in
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
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
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
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___123_8977.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____8980 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____8996) ->
             let uu____8997 =
               let uu____8998 =
                 let uu____9001 = FStar_TypeChecker_Env.get_range env1  in
                 ((Prims.strcat "Implicit argument: " msg), uu____9001)  in
               FStar_Errors.Error uu____8998  in
             Prims.raise uu____8997
          in
       match uu____8980 with
       | (t,c,g) ->
           let uu____9011 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____9011
           then (t, (c.FStar_Syntax_Syntax.lcomp_res_typ), g)
           else
             (let uu____9018 =
                let uu____9019 =
                  let uu____9022 =
                    let uu____9023 = FStar_Syntax_Print.term_to_string e  in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____9023
                     in
                  let uu____9024 = FStar_TypeChecker_Env.get_range env1  in
                  (uu____9022, uu____9024)  in
                FStar_Errors.Error uu____9019  in
              Prims.raise uu____9018))
  
let level_of_type_fail env e t =
  let uu____9045 =
    let uu____9046 =
      let uu____9049 =
        let uu____9050 = FStar_Syntax_Print.term_to_string e  in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____9050 t
         in
      let uu____9051 = FStar_TypeChecker_Env.get_range env  in
      (uu____9049, uu____9051)  in
    FStar_Errors.Error uu____9046  in
  Prims.raise uu____9045 
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____9068 =
            let uu____9069 = FStar_Syntax_Util.unrefine t1  in
            uu____9069.FStar_Syntax_Syntax.n  in
          match uu____9068 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____9073 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____9076 = FStar_Syntax_Util.type_u ()  in
                 match uu____9076 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___126_9082 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___126_9082.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___126_9082.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___126_9082.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___126_9082.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___126_9082.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___126_9082.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___126_9082.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___126_9082.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___126_9082.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___126_9082.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___126_9082.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___126_9082.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___126_9082.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___126_9082.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___126_9082.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___126_9082.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___126_9082.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___126_9082.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___126_9082.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___126_9082.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___126_9082.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___126_9082.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___126_9082.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____9086 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____9086
                       | uu____9087 ->
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
      let uu____9096 =
        let uu____9097 = FStar_Syntax_Subst.compress e  in
        uu____9097.FStar_Syntax_Syntax.n  in
      match uu____9096 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____9106 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____9117) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____9142,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____9157) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9164 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9164 with | (uu____9173,t) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____9175,FStar_Util.Inl t,uu____9177) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____9196,FStar_Util.Inr c,uu____9198) ->
          FStar_TypeChecker_Env.result_typ env c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____9228;
             FStar_Syntax_Syntax.pos = uu____9229;
             FStar_Syntax_Syntax.vars = uu____9230;_},us)
          ->
          let uu____9236 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9236 with
           | (us',t) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____9252 =
                     let uu____9253 =
                       let uu____9256 = FStar_TypeChecker_Env.get_range env
                          in
                       ("Unexpected number of universe instantiations",
                         uu____9256)
                        in
                     FStar_Errors.Error uu____9253  in
                   Prims.raise uu____9252)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____9264 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____9265 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____9273) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____9290 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9290 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____9301  ->
                      match uu____9301 with
                      | (b,uu____9305) ->
                          let uu____9306 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____9306) bs1
                  in
               let u_res =
                 let res = FStar_TypeChecker_Env.result_typ env c1  in
                 let uu____9309 = universe_of_aux env res  in
                 level_of_type env res uu____9309  in
               let u_c =
                 let uu____9311 = FStar_TypeChecker_Util.effect_repr env c1
                    in
                 match uu____9311 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____9314 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____9314
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)) None
                 e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2  in
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
                let uu____9400 = universe_of_aux env hd3  in
                (uu____9400, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____9410,hd4::uu____9412) ->
                let uu____9459 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____9459 with
                 | (uu____9469,uu____9470,hd5) ->
                     let uu____9486 = FStar_Syntax_Util.head_and_args hd5  in
                     (match uu____9486 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____9521 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____9523 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____9523 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____9558 ->
                let uu____9559 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                (match uu____9559 with
                 | (env1,uu____9573) ->
                     let env2 =
                       let uu___127_9577 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___127_9577.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___127_9577.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___127_9577.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___127_9577.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___127_9577.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___127_9577.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___127_9577.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___127_9577.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___127_9577.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___127_9577.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___127_9577.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___127_9577.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___127_9577.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___127_9577.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___127_9577.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___127_9577.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___127_9577.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___127_9577.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___127_9577.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___127_9577.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___127_9577.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     ((let uu____9579 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____9579
                       then
                         let uu____9580 =
                           let uu____9581 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____9581  in
                         let uu____9582 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____9580 uu____9582
                       else ());
                      (let uu____9584 = tc_term env2 hd3  in
                       match uu____9584 with
                       | (uu____9597,{
                                       FStar_Syntax_Syntax.lcomp_name =
                                         uu____9598;
                                       FStar_Syntax_Syntax.lcomp_univs =
                                         uu____9599;
                                       FStar_Syntax_Syntax.lcomp_indices =
                                         uu____9600;
                                       FStar_Syntax_Syntax.lcomp_res_typ = t;
                                       FStar_Syntax_Syntax.lcomp_cflags =
                                         uu____9602;
                                       FStar_Syntax_Syntax.lcomp_as_comp =
                                         uu____9603;_},g)
                           ->
                           ((let uu____9618 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____9618 Prims.ignore);
                            (t, args1)))))
             in
          let uu____9626 = type_of_head true hd1 args  in
          (match uu____9626 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____9655 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____9655 with
                | (bs,res) ->
                    let res1 = FStar_TypeChecker_Env.result_typ env res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____9686 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____9686)))
      | FStar_Syntax_Syntax.Tm_match (uu____9689,hd1::uu____9691) ->
          let uu____9738 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____9738 with
           | (uu____9741,uu____9742,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____9758,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____9792 = universe_of_aux env e  in
      level_of_type env e uu____9792
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____9805 = tc_binders env tps  in
      match uu____9805 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
  