open Prims
let instantiate_both : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___83_4 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___83_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___83_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___83_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___83_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___83_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___83_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___83_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___83_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___83_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___83_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___83_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___83_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___83_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___83_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___83_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___83_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___83_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___83_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___83_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___83_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___83_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___83_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___83_4.FStar_TypeChecker_Env.qname_and_index)
    }
  
let no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___84_8 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___84_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___84_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___84_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___84_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___84_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___84_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___84_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___84_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___84_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___84_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___84_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___84_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___84_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___84_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___84_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___84_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___84_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___84_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___84_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___84_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___84_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___84_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___84_8.FStar_TypeChecker_Env.qname_and_index)
    }
  
let mk_lex_list :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun vs  ->
    FStar_List.fold_right
      (fun v  ->
         fun tl  ->
           let r =
             match tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange with
             | true  -> v.FStar_Syntax_Syntax.pos
             | uu____33 ->
                 FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos
                   tl.FStar_Syntax_Syntax.pos
              in
           let uu____34 =
             let uu____35 =
               let uu____36 = FStar_Syntax_Syntax.as_arg v  in
               let uu____37 =
                 let uu____39 = FStar_Syntax_Syntax.as_arg tl  in [uu____39]
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
                let t =
                  match try_norm with | true  -> norm env t | uu____103 -> t
                   in
                let fvs' = FStar_Syntax_Free.names t  in
                let uu____106 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____106 with
                 | None  -> t
                 | Some x ->
                     (match Prims.op_Negation try_norm with
                      | true  -> aux true t
                      | uu____110 ->
                          let fail uu____114 =
                            let msg =
                              match head_opt with
                              | None  ->
                                  let uu____116 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  FStar_Util.format1
                                    "Bound variables '%s' escapes; add a type annotation"
                                    uu____116
                              | Some head ->
                                  let uu____118 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____119 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env head
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
                            FStar_TypeChecker_Rel.try_teq env t s  in
                          (match uu____132 with
                           | Some g ->
                               (FStar_TypeChecker_Rel.force_trivial_guard env
                                  g;
                                s)
                           | uu____136 -> fail ())))
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
      fun v  ->
        let uu____167 = FStar_Syntax_Syntax.is_null_binder b  in
        match uu____167 with
        | true  -> s
        | uu____168 -> (FStar_Syntax_Syntax.NT ((Prims.fst b), v)) :: s
  
let set_lcomp_result :
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___85_181 = lc  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___85_181.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___85_181.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____182  ->
             let uu____183 = lc.FStar_Syntax_Syntax.comp ()  in
             FStar_Syntax_Util.set_result_typ uu____183 t)
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
            let uu____222 =
              let uu____223 = FStar_Syntax_Subst.compress t  in
              uu____223.FStar_Syntax_Syntax.n  in
            match uu____222 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____226,c) ->
                let uu____238 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                (match uu____238 with
                 | true  ->
                     let t =
                       FStar_All.pipe_left FStar_Syntax_Util.unrefine
                         (FStar_Syntax_Util.comp_result c)
                        in
                     let uu____240 =
                       let uu____241 = FStar_Syntax_Subst.compress t  in
                       uu____241.FStar_Syntax_Syntax.n  in
                     (match uu____240 with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Syntax_Const.unit_lid
                          -> false
                      | FStar_Syntax_Syntax.Tm_constant uu____245 -> false
                      | uu____246 -> true)
                 | uu____247 -> false)
            | uu____248 -> true  in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____251 =
                  let uu____254 =
                    (let uu____255 = should_return t  in
                     Prims.op_Negation uu____255) ||
                      (let uu____256 =
                         FStar_TypeChecker_Env.should_verify env  in
                       Prims.op_Negation uu____256)
                     in
                  match uu____254 with
                  | true  -> FStar_Syntax_Syntax.mk_Total t
                  | uu____259 -> FStar_TypeChecker_Util.return_value env t e
                   in
                FStar_Syntax_Util.lcomp_of_comp uu____251
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____264 =
            let uu____268 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____268 with
            | None  -> let uu____273 = memo_tk e t  in (uu____273, lc, guard)
            | Some t' ->
                ((let uu____276 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High  in
                  match uu____276 with
                  | true  ->
                      let uu____277 = FStar_Syntax_Print.term_to_string t  in
                      let uu____278 = FStar_Syntax_Print.term_to_string t'
                         in
                      FStar_Util.print2
                        "Computed return type %s; expected type %s\n"
                        uu____277 uu____278
                  | uu____279 -> ());
                 (let uu____280 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t'
                     in
                  match uu____280 with
                  | (e,lc) ->
                      let t = lc.FStar_Syntax_Syntax.res_typ  in
                      let uu____291 =
                        FStar_TypeChecker_Util.check_and_ascribe env e t t'
                         in
                      (match uu____291 with
                       | (e,g) ->
                           ((let uu____300 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             match uu____300 with
                             | true  ->
                                 let uu____301 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 let uu____302 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 let uu____303 =
                                   FStar_TypeChecker_Rel.guard_to_string env
                                     g
                                    in
                                 let uu____304 =
                                   FStar_TypeChecker_Rel.guard_to_string env
                                     guard
                                    in
                                 FStar_Util.print4
                                   "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                   uu____301 uu____302 uu____303 uu____304
                             | uu____305 -> ());
                            (let msg =
                               let uu____310 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               match uu____310 with
                               | true  -> None
                               | uu____316 ->
                                   FStar_All.pipe_left
                                     (fun _0_28  -> Some _0_28)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env t t')
                                in
                             let g = FStar_TypeChecker_Rel.conj_guard g guard
                                in
                             let uu____325 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e lc g
                                in
                             match uu____325 with
                             | (lc,g) ->
                                 let uu____333 = memo_tk e t'  in
                                 (uu____333, (set_lcomp_result lc t'), g))))))
             in
          match uu____264 with
          | (e,lc,g) ->
              ((let uu____341 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                match uu____341 with
                | true  ->
                    let uu____342 = FStar_Syntax_Print.lcomp_to_string lc  in
                    FStar_Util.print1 "Return comp type is %s\n" uu____342
                | uu____343 -> ());
               (e, lc, g))
  
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
        let uu____359 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____359 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____365 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____365 with
             | (e,lc) -> FStar_TypeChecker_Util.weaken_result_typ env e lc t)
  
let check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp Prims.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
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
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____404))
                     in
                  (match uu____403 with
                   | true  ->
                       let uu____406 =
                         FStar_Syntax_Util.ml_comp
                           (FStar_Syntax_Util.comp_result c)
                           e.FStar_Syntax_Syntax.pos
                          in
                       Some uu____406
                   | uu____407 ->
                       let uu____408 =
                         FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                       (match uu____408 with
                        | true  -> None
                        | uu____410 ->
                            let uu____411 = FStar_Syntax_Util.is_pure_comp c
                               in
                            (match uu____411 with
                             | true  ->
                                 let uu____413 =
                                   FStar_Syntax_Syntax.mk_Total
                                     (FStar_Syntax_Util.comp_result c)
                                    in
                                 Some uu____413
                             | uu____414 ->
                                 let uu____415 =
                                   FStar_Syntax_Util.is_pure_or_ghost_comp c
                                    in
                                 (match uu____415 with
                                  | true  ->
                                      let uu____417 =
                                        FStar_Syntax_Syntax.mk_GTotal
                                          (FStar_Syntax_Util.comp_result c)
                                         in
                                      Some uu____417
                                  | uu____418 -> None))))
               in
            (match expected_c_opt with
             | None  ->
                 let uu____422 = norm_c env c  in
                 (e, uu____422, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____425 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                   match uu____425 with
                   | true  ->
                       let uu____426 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____427 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____428 =
                         FStar_Syntax_Print.comp_to_string expected_c  in
                       FStar_Util.print3
                         "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                         uu____426 uu____427 uu____428
                   | uu____429 -> ());
                  (let c = norm_c env c  in
                   (let uu____432 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                    match uu____432 with
                    | true  ->
                        let uu____433 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____434 = FStar_Syntax_Print.comp_to_string c
                           in
                        let uu____435 =
                          FStar_Syntax_Print.comp_to_string expected_c  in
                        FStar_Util.print3
                          "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                          uu____433 uu____434 uu____435
                    | uu____436 -> ());
                   (let uu____437 =
                      FStar_TypeChecker_Util.check_comp env e c expected_c
                       in
                    match uu____437 with
                    | (e,uu____445,g) ->
                        let g =
                          let uu____448 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_TypeChecker_Util.label_guard uu____448
                            "could not prove post-condition" g
                           in
                        ((let uu____450 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low
                             in
                          match uu____450 with
                          | true  ->
                              let uu____451 =
                                FStar_Range.string_of_range
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____452 =
                                FStar_TypeChecker_Rel.guard_to_string env g
                                 in
                              FStar_Util.print2
                                "(%s) DONE check_expected_effect; guard is: %s\n"
                                uu____451 uu____452
                          | uu____453 -> ());
                         (let e =
                            FStar_TypeChecker_Util.maybe_lift env e
                              (FStar_Syntax_Util.comp_effect_name c)
                              (FStar_Syntax_Util.comp_effect_name expected_c)
                              (FStar_Syntax_Util.comp_result c)
                             in
                          (e, expected_c, g)))))))
  
let no_logical_guard env uu____474 =
  match uu____474 with
  | (te,kt,f) ->
      let uu____481 = FStar_TypeChecker_Rel.guard_form f  in
      (match uu____481 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f ->
           let uu____486 =
             let uu____487 =
               let uu____490 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f
                  in
               let uu____491 = FStar_TypeChecker_Env.get_range env  in
               (uu____490, uu____491)  in
             FStar_Errors.Error uu____487  in
           Prims.raise uu____486)
  
let print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____498 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____498 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____501 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____501
  
let check_smt_pat env t bs c =
  let uu____536 = FStar_Syntax_Util.is_smt_lemma t  in
  match uu____536 with
  | true  ->
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Comp
           { FStar_Syntax_Syntax.comp_univs = uu____537;
             FStar_Syntax_Syntax.effect_name = uu____538;
             FStar_Syntax_Syntax.result_typ = uu____539;
             FStar_Syntax_Syntax.effect_args =
               _pre::_post::(pats,uu____543)::[];
             FStar_Syntax_Syntax.flags = uu____544;_}
           ->
           let pat_vars =
             let uu____578 =
               FStar_TypeChecker_Normalize.normalize
                 [FStar_TypeChecker_Normalize.Beta] env pats
                in
             FStar_Syntax_Free.names uu____578  in
           let uu____579 =
             FStar_All.pipe_right bs
               (FStar_Util.find_opt
                  (fun uu____591  ->
                     match uu____591 with
                     | (b,uu____595) ->
                         let uu____596 = FStar_Util.set_mem b pat_vars  in
                         Prims.op_Negation uu____596))
              in
           (match uu____579 with
            | None  -> ()
            | Some (x,uu____600) ->
                let uu____603 =
                  let uu____604 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____604
                   in
                FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____603)
       | uu____605 -> failwith "Impossible")
  | uu____606 -> () 
let guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____626 =
          let uu____627 = FStar_TypeChecker_Env.should_verify env  in
          Prims.op_Negation uu____627  in
        match uu____626 with
        | true  -> env.FStar_TypeChecker_Env.letrecs
        | uu____631 ->
            (match env.FStar_TypeChecker_Env.letrecs with
             | [] -> []
             | letrecs ->
                 let r = FStar_TypeChecker_Env.get_range env  in
                 let env =
                   let uu___86_645 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___86_645.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___86_645.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___86_645.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___86_645.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___86_645.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___86_645.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___86_645.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___86_645.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___86_645.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___86_645.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___86_645.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___86_645.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs = [];
                     FStar_TypeChecker_Env.top_level =
                       (uu___86_645.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___86_645.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___86_645.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___86_645.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___86_645.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax =
                       (uu___86_645.FStar_TypeChecker_Env.lax);
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___86_645.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.type_of =
                       (uu___86_645.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___86_645.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___86_645.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qname_and_index =
                       (uu___86_645.FStar_TypeChecker_Env.qname_and_index)
                   }  in
                 let precedes =
                   FStar_TypeChecker_Util.fvar_const env
                     FStar_Syntax_Const.precedes_lid
                    in
                 let decreases_clause bs c =
                   let filter_types_and_functions bs =
                     FStar_All.pipe_right bs
                       (FStar_List.collect
                          (fun uu____668  ->
                             match uu____668 with
                             | (b,uu____673) ->
                                 let t =
                                   let uu____675 =
                                     FStar_Syntax_Util.unrefine
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   unfold_whnf env uu____675  in
                                 (match t.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_type _
                                    |FStar_Syntax_Syntax.Tm_arrow _ -> []
                                  | uu____679 ->
                                      let uu____680 =
                                        FStar_Syntax_Syntax.bv_to_name b  in
                                      [uu____680])))
                      in
                   let as_lex_list dec =
                     let uu____685 = FStar_Syntax_Util.head_and_args dec  in
                     match uu____685 with
                     | (head,uu____696) ->
                         (match head.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.lexcons_lid
                              -> dec
                          | uu____712 -> mk_lex_list [dec])
                      in
                   let cflags = FStar_Syntax_Util.comp_flags c  in
                   let uu____715 =
                     FStar_All.pipe_right cflags
                       (FStar_List.tryFind
                          (fun uu___78_719  ->
                             match uu___78_719 with
                             | FStar_Syntax_Syntax.DECREASES uu____720 ->
                                 true
                             | uu____723 -> false))
                      in
                   match uu____715 with
                   | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                       as_lex_list dec
                   | uu____727 ->
                       let xs =
                         FStar_All.pipe_right bs filter_types_and_functions
                          in
                       (match xs with
                        | x::[] -> x
                        | uu____733 -> mk_lex_list xs)
                    in
                 let previous_dec = decreases_clause actuals expected_c  in
                 let guard_one_letrec uu____745 =
                   match uu____745 with
                   | (l,t) ->
                       let uu____754 =
                         let uu____755 = FStar_Syntax_Subst.compress t  in
                         uu____755.FStar_Syntax_Syntax.n  in
                       (match uu____754 with
                        | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                            let formals =
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____788  ->
                                      match uu____788 with
                                      | (x,imp) ->
                                          let uu____795 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          (match uu____795 with
                                           | true  ->
                                               let uu____798 =
                                                 let uu____799 =
                                                   let uu____801 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       x
                                                      in
                                                   Some uu____801  in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____799
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               (uu____798, imp)
                                           | uu____802 -> (x, imp))))
                               in
                            let uu____803 =
                              FStar_Syntax_Subst.open_comp formals c  in
                            (match uu____803 with
                             | (formals,c) ->
                                 let dec = decreases_clause formals c  in
                                 let precedes =
                                   let uu____816 =
                                     let uu____817 =
                                       let uu____818 =
                                         FStar_Syntax_Syntax.as_arg dec  in
                                       let uu____819 =
                                         let uu____821 =
                                           FStar_Syntax_Syntax.as_arg
                                             previous_dec
                                            in
                                         [uu____821]  in
                                       uu____818 :: uu____819  in
                                     FStar_Syntax_Syntax.mk_Tm_app precedes
                                       uu____817
                                      in
                                   uu____816 None r  in
                                 let uu____826 = FStar_Util.prefix formals
                                    in
                                 (match uu____826 with
                                  | (bs,(last,imp)) ->
                                      let last =
                                        let uu___87_852 = last  in
                                        let uu____853 =
                                          FStar_Syntax_Util.refine last
                                            precedes
                                           in
                                        {
                                          FStar_Syntax_Syntax.ppname =
                                            (uu___87_852.FStar_Syntax_Syntax.ppname);
                                          FStar_Syntax_Syntax.index =
                                            (uu___87_852.FStar_Syntax_Syntax.index);
                                          FStar_Syntax_Syntax.sort =
                                            uu____853
                                        }  in
                                      let refined_formals =
                                        FStar_List.append bs [(last, imp)]
                                         in
                                      let t' =
                                        FStar_Syntax_Util.arrow
                                          refined_formals c
                                         in
                                      ((let uu____870 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Low
                                           in
                                        match uu____870 with
                                        | true  ->
                                            let uu____871 =
                                              FStar_Syntax_Print.lbname_to_string
                                                l
                                               in
                                            let uu____872 =
                                              FStar_Syntax_Print.term_to_string
                                                t
                                               in
                                            let uu____873 =
                                              FStar_Syntax_Print.term_to_string
                                                t'
                                               in
                                            FStar_Util.print3
                                              "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                              uu____871 uu____872 uu____873
                                        | uu____874 -> ());
                                       (l, t'))))
                        | uu____877 ->
                            Prims.raise
                              (FStar_Errors.Error
                                 ("Annotated type of 'let rec' must be an arrow",
                                   (t.FStar_Syntax_Syntax.pos))))
                    in
                 FStar_All.pipe_right letrecs
                   (FStar_List.map guard_one_letrec))
  
let rec tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___88_1141 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___88_1141.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___88_1141.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___88_1141.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___88_1141.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___88_1141.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___88_1141.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___88_1141.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___88_1141.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___88_1141.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___88_1141.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___88_1141.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___88_1141.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___88_1141.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___88_1141.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___88_1141.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___88_1141.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___88_1141.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___88_1141.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___88_1141.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___88_1141.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___88_1141.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___88_1141.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___88_1141.FStar_TypeChecker_Env.qname_and_index)
         }) e

and tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env =
        match e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange with
        | true  -> env
        | uu____1148 ->
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      (let uu____1150 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       match uu____1150 with
       | true  ->
           let uu____1151 =
             let uu____1152 = FStar_TypeChecker_Env.get_range env  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1152  in
           let uu____1153 = FStar_Syntax_Print.tag_of_term e  in
           FStar_Util.print2 "%s (%s)\n" uu____1151 uu____1153
       | uu____1154 -> ());
      (let top = FStar_Syntax_Subst.compress e  in
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
           -> tc_value env e
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1198 = tc_tot_or_gtot_term env e  in
           (match uu____1198 with
            | (e,c,g) ->
                let g =
                  let uu___89_1209 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___89_1209.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___89_1209.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___89_1209.FStar_TypeChecker_Env.implicits)
                  }  in
                (e, c, g))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1222 = FStar_Syntax_Util.type_u ()  in
           (match uu____1222 with
            | (t,u) ->
                let uu____1230 = tc_check_tot_or_gtot_term env e t  in
                (match uu____1230 with
                 | (e,c,g) ->
                     let uu____1240 =
                       let uu____1249 =
                         FStar_TypeChecker_Env.clear_expected_typ env  in
                       match uu____1249 with
                       | (env,uu____1262) -> tc_pats env pats  in
                     (match uu____1240 with
                      | (pats,g') ->
                          let g' =
                            let uu___90_1283 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___90_1283.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___90_1283.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___90_1283.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____1284 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e,
                                    (FStar_Syntax_Syntax.Meta_pattern pats))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____1295 =
                            FStar_TypeChecker_Rel.conj_guard g g'  in
                          (uu____1284, c, uu____1295))))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1303 =
             let uu____1304 = FStar_Syntax_Subst.compress e  in
             uu____1304.FStar_Syntax_Syntax.n  in
           (match uu____1303 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1310,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1312;
                               FStar_Syntax_Syntax.lbtyp = uu____1313;
                               FStar_Syntax_Syntax.lbeff = uu____1314;
                               FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
                ->
                let uu____1332 =
                  let uu____1336 =
                    FStar_TypeChecker_Env.set_expected_typ env
                      FStar_TypeChecker_Common.t_unit
                     in
                  tc_term uu____1336 e1  in
                (match uu____1332 with
                 | (e1,c1,g1) ->
                     let uu____1343 = tc_term env e2  in
                     (match uu____1343 with
                      | (e2,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind
                              e1.FStar_Syntax_Syntax.pos env (Some e1) c1
                              (None, c2)
                             in
                          let e1 =
                            FStar_TypeChecker_Util.maybe_lift env e1
                              c1.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ
                             in
                          let e2 =
                            FStar_TypeChecker_Util.maybe_lift env e2
                              c2.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ
                             in
                          let e =
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
                                            e1)
                                         in
                                      [uu____1378]  in
                                    (false, uu____1376)  in
                                  (uu____1372, e2)  in
                                FStar_Syntax_Syntax.Tm_let uu____1364  in
                              FStar_Syntax_Syntax.mk uu____1363  in
                            uu____1360
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e =
                            FStar_TypeChecker_Util.maybe_monadic env e
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          let e =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e,
                                    (FStar_Syntax_Syntax.Meta_desugared
                                       FStar_Syntax_Syntax.Sequence))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____1408 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e, c, uu____1408)))
            | uu____1411 ->
                let uu____1412 = tc_term env e  in
                (match uu____1412 with
                 | (e,c,g) ->
                     let e =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (e,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Sequence))))
                         (Some
                            ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_monadic uu____1436) -> tc_term env e
       | FStar_Syntax_Syntax.Tm_meta (e,m) ->
           let uu____1451 = tc_term env e  in
           (match uu____1451 with
            | (e,c,g) ->
                let e =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos
                   in
                (e, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e,FStar_Util.Inr expected_c,uu____1476) ->
           let uu____1495 = FStar_TypeChecker_Env.clear_expected_typ env  in
           (match uu____1495 with
            | (env0,uu____1503) ->
                let uu____1506 = tc_comp env0 expected_c  in
                (match uu____1506 with
                 | (expected_c,uu____1514,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c  in
                     let uu____1519 =
                       let uu____1523 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____1523 e  in
                     (match uu____1519 with
                      | (e,c',g') ->
                          let uu____1530 =
                            let uu____1534 =
                              let uu____1537 = c'.FStar_Syntax_Syntax.comp ()
                                 in
                              (e, uu____1537)  in
                            check_expected_effect env0 (Some expected_c)
                              uu____1534
                             in
                          (match uu____1530 with
                           | (e,expected_c,g'') ->
                               let e =
                                 (FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_ascribed
                                       (e, (FStar_Util.Inl t_res),
                                         (Some
                                            (FStar_Syntax_Util.comp_effect_name
                                               expected_c)))))
                                   (Some (t_res.FStar_Syntax_Syntax.n))
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c
                                  in
                               let f =
                                 let uu____1572 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1572
                                  in
                               let uu____1573 =
                                 comp_check_expected_typ env e lc  in
                               (match uu____1573 with
                                | (e,c,f2) ->
                                    let uu____1583 =
                                      FStar_TypeChecker_Rel.conj_guard f f2
                                       in
                                    (e, c, uu____1583))))))
       | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t,uu____1586) ->
           let uu____1605 = FStar_Syntax_Util.type_u ()  in
           (match uu____1605 with
            | (k,u) ->
                let uu____1613 = tc_check_tot_or_gtot_term env t k  in
                (match uu____1613 with
                 | (t,uu____1621,f) ->
                     let uu____1623 =
                       let uu____1627 =
                         FStar_TypeChecker_Env.set_expected_typ env t  in
                       tc_term uu____1627 e  in
                     (match uu____1623 with
                      | (e,c,g) ->
                          let uu____1634 =
                            let uu____1637 =
                              FStar_TypeChecker_Env.set_range env
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1640  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1637 e c f
                             in
                          (match uu____1634 with
                           | (c,f) ->
                               let uu____1646 =
                                 let uu____1650 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e, (FStar_Util.Inl t),
                                           (Some
                                              (c.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env uu____1650 c  in
                               (match uu____1646 with
                                | (e,c,f2) ->
                                    let uu____1672 =
                                      let uu____1673 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f
                                        uu____1673
                                       in
                                    (e, c, uu____1672))))))
       | FStar_Syntax_Syntax.Tm_app
         ({
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
              (FStar_Const.Const_reify );
            FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
            FStar_Syntax_Syntax.vars = _;_},a::hd::rest)
         |FStar_Syntax_Syntax.Tm_app
         ({
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
              (FStar_Const.Const_reflect _);
            FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
            FStar_Syntax_Syntax.vars = _;_},a::hd::rest)
           ->
           let rest = hd :: rest  in
           let uu____1750 = FStar_Syntax_Util.head_and_args top  in
           (match uu____1750 with
            | (unary_op,uu____1764) ->
                let head =
                  let uu____1782 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (Prims.fst a).FStar_Syntax_Syntax.pos
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1782
                   in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head, rest))) None
                    top.FStar_Syntax_Syntax.pos
                   in
                tc_term env t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1826;
              FStar_Syntax_Syntax.pos = uu____1827;
              FStar_Syntax_Syntax.vars = uu____1828;_},(e,aqual)::[])
           ->
           ((match FStar_Option.isSome aqual with
             | true  ->
                 FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "Qualifier on argument to reify is irrelevant and will be ignored"
             | uu____1853 -> ());
            (let uu____1854 =
               let uu____1858 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               match uu____1858 with | (env0,uu____1866) -> tc_term env0 e
                in
             match uu____1854 with
             | (e,c,g) ->
                 let uu____1875 = FStar_Syntax_Util.head_and_args top  in
                 (match uu____1875 with
                  | (reify_op,uu____1889) ->
                      let u_c =
                        let uu____1905 =
                          tc_term env c.FStar_Syntax_Syntax.res_typ  in
                        match uu____1905 with
                        | (uu____1909,c',uu____1911) ->
                            let uu____1912 =
                              let uu____1913 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ
                                 in
                              uu____1913.FStar_Syntax_Syntax.n  in
                            (match uu____1912 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____1917 ->
                                 let uu____1918 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____1918 with
                                  | (t,u) ->
                                      let g_opt =
                                        FStar_TypeChecker_Rel.try_teq env
                                          c'.FStar_Syntax_Syntax.res_typ t
                                         in
                                      ((match g_opt with
                                        | Some g' ->
                                            FStar_TypeChecker_Rel.force_trivial_guard
                                              env g'
                                        | None  ->
                                            let uu____1927 =
                                              let uu____1928 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c'
                                                 in
                                              let uu____1929 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ
                                                 in
                                              let uu____1930 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ
                                                 in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____1928 uu____1929
                                                uu____1930
                                               in
                                            failwith uu____1927);
                                       u)))
                         in
                      let repr = FStar_TypeChecker_Util.reify_comp env c u_c
                         in
                      let e =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos
                         in
                      let c =
                        let uu____1953 = FStar_Syntax_Syntax.mk_Total repr
                           in
                        FStar_All.pipe_right uu____1953
                          FStar_Syntax_Util.lcomp_of_comp
                         in
                      let uu____1954 = comp_check_expected_typ env e c  in
                      (match uu____1954 with
                       | (e,c,g') ->
                           let uu____1964 =
                             FStar_TypeChecker_Rel.conj_guard g g'  in
                           (e, c, uu____1964)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____1966;
              FStar_Syntax_Syntax.pos = uu____1967;
              FStar_Syntax_Syntax.vars = uu____1968;_},(e,aqual)::[])
           ->
           ((match FStar_Option.isSome aqual with
             | true  ->
                 FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "Qualifier on argument to reflect is irrelevant and will be ignored"
             | uu____1993 -> ());
            (let no_reflect uu____2000 =
               let uu____2001 =
                 let uu____2002 =
                   let uu____2005 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str
                      in
                   (uu____2005, (e.FStar_Syntax_Syntax.pos))  in
                 FStar_Errors.Error uu____2002  in
               Prims.raise uu____2001  in
             let uu____2009 = FStar_Syntax_Util.head_and_args top  in
             match uu____2009 with
             | (reflect_op,uu____2023) ->
                 let uu____2038 = FStar_TypeChecker_Env.effect_decl_opt env l
                    in
                 (match uu____2038 with
                  | None  -> no_reflect ()
                  | Some ed ->
                      let uu____2044 =
                        let uu____2045 =
                          FStar_All.pipe_right
                            ed.FStar_Syntax_Syntax.qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____2045  in
                      (match uu____2044 with
                       | true  -> no_reflect ()
                       | uu____2050 ->
                           let uu____2051 =
                             FStar_TypeChecker_Env.clear_expected_typ env  in
                           (match uu____2051 with
                            | (env_no_ex,topt) ->
                                let uu____2062 =
                                  let u = FStar_TypeChecker_Env.new_u_univ ()
                                     in
                                  let repr =
                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                      [u] env ed
                                      ([], (ed.FStar_Syntax_Syntax.repr))
                                     in
                                  let t =
                                    let uu____2077 =
                                      let uu____2080 =
                                        let uu____2081 =
                                          let uu____2091 =
                                            let uu____2093 =
                                              FStar_Syntax_Syntax.as_arg
                                                FStar_Syntax_Syntax.tun
                                               in
                                            let uu____2094 =
                                              let uu____2096 =
                                                FStar_Syntax_Syntax.as_arg
                                                  FStar_Syntax_Syntax.tun
                                                 in
                                              [uu____2096]  in
                                            uu____2093 :: uu____2094  in
                                          (repr, uu____2091)  in
                                        FStar_Syntax_Syntax.Tm_app uu____2081
                                         in
                                      FStar_Syntax_Syntax.mk uu____2080  in
                                    uu____2077 None
                                      top.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____2106 =
                                    let uu____2110 =
                                      let uu____2111 =
                                        FStar_TypeChecker_Env.clear_expected_typ
                                          env
                                         in
                                      FStar_All.pipe_right uu____2111
                                        Prims.fst
                                       in
                                    tc_tot_or_gtot_term uu____2110 t  in
                                  match uu____2106 with
                                  | (t,uu____2128,g) ->
                                      let uu____2130 =
                                        let uu____2131 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____2131.FStar_Syntax_Syntax.n  in
                                      (match uu____2130 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____2142,(res,uu____2144)::
                                            (wp,uu____2146)::[])
                                           -> (t, res, wp, g)
                                       | uu____2180 -> failwith "Impossible")
                                   in
                                (match uu____2062 with
                                 | (expected_repr_typ,res_typ,wp,g0) ->
                                     let uu____2204 =
                                       let uu____2207 =
                                         tc_tot_or_gtot_term env_no_ex e  in
                                       match uu____2207 with
                                       | (e,c,g) ->
                                           ((let uu____2217 =
                                               let uu____2218 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   c
                                                  in
                                               FStar_All.pipe_left
                                                 Prims.op_Negation uu____2218
                                                in
                                             match uu____2217 with
                                             | true  ->
                                                 FStar_TypeChecker_Err.add_errors
                                                   env
                                                   [("Expected Tot, got a GTot computation",
                                                      (e.FStar_Syntax_Syntax.pos))]
                                             | uu____2223 -> ());
                                            (let uu____2224 =
                                               FStar_TypeChecker_Rel.try_teq
                                                 env_no_ex
                                                 c.FStar_Syntax_Syntax.res_typ
                                                 expected_repr_typ
                                                in
                                             match uu____2224 with
                                             | None  ->
                                                 ((let uu____2229 =
                                                     let uu____2233 =
                                                       let uu____2236 =
                                                         let uu____2237 =
                                                           FStar_Syntax_Print.term_to_string
                                                             ed.FStar_Syntax_Syntax.repr
                                                            in
                                                         let uu____2238 =
                                                           FStar_Syntax_Print.term_to_string
                                                             c.FStar_Syntax_Syntax.res_typ
                                                            in
                                                         FStar_Util.format2
                                                           "Expected an instance of %s; got %s"
                                                           uu____2237
                                                           uu____2238
                                                          in
                                                       (uu____2236,
                                                         (e.FStar_Syntax_Syntax.pos))
                                                        in
                                                     [uu____2233]  in
                                                   FStar_TypeChecker_Err.add_errors
                                                     env uu____2229);
                                                  (let uu____2243 =
                                                     FStar_TypeChecker_Rel.conj_guard
                                                       g g0
                                                      in
                                                   (e, uu____2243)))
                                             | Some g' ->
                                                 let uu____2245 =
                                                   let uu____2246 =
                                                     FStar_TypeChecker_Rel.conj_guard
                                                       g g0
                                                      in
                                                   FStar_TypeChecker_Rel.conj_guard
                                                     g' uu____2246
                                                    in
                                                 (e, uu____2245)))
                                        in
                                     (match uu____2204 with
                                      | (e,g) ->
                                          let c =
                                            let uu____2253 =
                                              let uu____2254 =
                                                let uu____2255 =
                                                  let uu____2256 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env res_typ
                                                     in
                                                  [uu____2256]  in
                                                let uu____2257 =
                                                  let uu____2263 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____2263]  in
                                                {
                                                  FStar_Syntax_Syntax.comp_univs
                                                    = uu____2255;
                                                  FStar_Syntax_Syntax.effect_name
                                                    =
                                                    (ed.FStar_Syntax_Syntax.mname);
                                                  FStar_Syntax_Syntax.result_typ
                                                    = res_typ;
                                                  FStar_Syntax_Syntax.effect_args
                                                    = uu____2257;
                                                  FStar_Syntax_Syntax.flags =
                                                    []
                                                }  in
                                              FStar_Syntax_Syntax.mk_Comp
                                                uu____2254
                                               in
                                            FStar_All.pipe_right uu____2253
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          let e =
                                            (FStar_Syntax_Syntax.mk
                                               (FStar_Syntax_Syntax.Tm_app
                                                  (reflect_op, [(e, aqual)])))
                                              (Some
                                                 (res_typ.FStar_Syntax_Syntax.n))
                                              top.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____2284 =
                                            comp_check_expected_typ env e c
                                             in
                                          (match uu____2284 with
                                           | (e,c,g') ->
                                               let uu____2294 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   g' g
                                                  in
                                               (e, c, uu____2294)))))))))
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let env0 = env  in
           let env =
             let uu____2313 =
               let uu____2314 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____2314 Prims.fst  in
             FStar_All.pipe_right uu____2313 instantiate_both  in
           ((let uu____2323 =
               FStar_TypeChecker_Env.debug env FStar_Options.High  in
             match uu____2323 with
             | true  ->
                 let uu____2324 =
                   FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos
                    in
                 let uu____2325 = FStar_Syntax_Print.term_to_string top  in
                 FStar_Util.print2 "(%s) Checking app %s\n" uu____2324
                   uu____2325
             | uu____2326 -> ());
            (let uu____2327 = tc_term (no_inst env) head  in
             match uu____2327 with
             | (head,chead,g_head) ->
                 let uu____2337 =
                   let uu____2341 =
                     (Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head)
                      in
                   match uu____2341 with
                   | true  ->
                       let uu____2345 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env head chead g_head args
                         uu____2345
                   | uu____2347 ->
                       let uu____2348 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_application_args env head chead g_head args
                         uu____2348
                    in
                 (match uu____2337 with
                  | (e,c,g) ->
                      ((let uu____2357 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Extreme
                           in
                        match uu____2357 with
                        | true  ->
                            let uu____2358 =
                              FStar_TypeChecker_Rel.print_pending_implicits g
                               in
                            FStar_Util.print1
                              "Introduced {%s} implicits in application\n"
                              uu____2358
                        | uu____2359 -> ());
                       (let c =
                          let uu____2361 =
                            ((FStar_TypeChecker_Env.should_verify env) &&
                               (let uu____2362 =
                                  FStar_Syntax_Util.is_lcomp_partial_return c
                                   in
                                Prims.op_Negation uu____2362))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                             in
                          match uu____2361 with
                          | true  ->
                              FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                env e c
                          | uu____2363 -> c  in
                        let uu____2364 = comp_check_expected_typ env0 e c  in
                        match uu____2364 with
                        | (e,c,g') ->
                            let gimp =
                              let uu____2375 =
                                let uu____2376 =
                                  FStar_Syntax_Subst.compress head  in
                                uu____2376.FStar_Syntax_Syntax.n  in
                              match uu____2375 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2380) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e, (c.FStar_Syntax_Syntax.res_typ),
                                      (head.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___91_2412 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___91_2412.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___91_2412.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___91_2412.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2437 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____2439 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____2439
                               in
                            ((let uu____2441 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              match uu____2441 with
                              | true  ->
                                  let uu____2442 =
                                    FStar_Syntax_Print.term_to_string e  in
                                  let uu____2443 =
                                    FStar_TypeChecker_Rel.guard_to_string env
                                      gres
                                     in
                                  FStar_Util.print2
                                    "Guard from application node %s is %s\n"
                                    uu____2442 uu____2443
                              | uu____2444 -> ());
                             (e, c, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2473 = FStar_TypeChecker_Env.clear_expected_typ env  in
           (match uu____2473 with
            | (env1,topt) ->
                let env1 = instantiate_both env1  in
                let uu____2485 = tc_term env1 e1  in
                (match uu____2485 with
                 | (e1,c1,g1) ->
                     let uu____2495 =
                       match topt with
                       | Some t -> (env, t)
                       | None  ->
                           let uu____2501 = FStar_Syntax_Util.type_u ()  in
                           (match uu____2501 with
                            | (k,uu____2507) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env k  in
                                let uu____2509 =
                                  FStar_TypeChecker_Env.set_expected_typ env
                                    res_t
                                   in
                                (uu____2509, res_t))
                        in
                     (match uu____2495 with
                      | (env_branches,res_t) ->
                          ((let uu____2516 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            match uu____2516 with
                            | true  ->
                                let uu____2517 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                FStar_Util.print1
                                  "Tm_match: expected type of branches is %s\n"
                                  uu____2517
                            | uu____2518 -> ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e1.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____2568 =
                              let uu____2571 =
                                FStar_List.fold_right
                                  (fun uu____2590  ->
                                     fun uu____2591  ->
                                       match (uu____2590, uu____2591) with
                                       | ((uu____2623,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2656 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), uu____2656))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____2571 with
                              | (cases,g) ->
                                  let uu____2677 =
                                    FStar_TypeChecker_Util.bind_cases env
                                      res_t cases
                                     in
                                  (uu____2677, g)
                               in
                            match uu____2568 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e1.FStar_Syntax_Syntax.pos env (Some e1)
                                    c1 ((Some guard_x), c_branches)
                                   in
                                let e =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____2730  ->
                                              match uu____2730 with
                                              | ((pat,wopt,br),uu____2746,lc,uu____2748)
                                                  ->
                                                  let uu____2755 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  (pat, wopt, uu____2755)))
                                       in
                                    let e =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_match
                                            (scrutinee, branches)))
                                        (Some
                                           ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let e =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env e
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    (FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_ascribed
                                          (e,
                                            (FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.eff_name)))))
                                      None e.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____2795 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  match uu____2795 with
                                  | true  -> mk_match e1
                                  | uu____2798 ->
                                      let e_match =
                                        let uu____2802 =
                                          FStar_Syntax_Syntax.bv_to_name
                                            guard_x
                                           in
                                        mk_match uu____2802  in
                                      let lb =
                                        let uu____2806 =
                                          FStar_TypeChecker_Env.norm_eff_name
                                            env
                                            c1.FStar_Syntax_Syntax.eff_name
                                           in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (FStar_Util.Inl guard_x);
                                          FStar_Syntax_Syntax.lbunivs = [];
                                          FStar_Syntax_Syntax.lbtyp =
                                            (c1.FStar_Syntax_Syntax.res_typ);
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____2806;
                                          FStar_Syntax_Syntax.lbdef = e1
                                        }  in
                                      let e =
                                        let uu____2810 =
                                          let uu____2813 =
                                            let uu____2814 =
                                              let uu____2822 =
                                                let uu____2823 =
                                                  let uu____2824 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      guard_x
                                                     in
                                                  [uu____2824]  in
                                                FStar_Syntax_Subst.close
                                                  uu____2823 e_match
                                                 in
                                              ((false, [lb]), uu____2822)  in
                                            FStar_Syntax_Syntax.Tm_let
                                              uu____2814
                                             in
                                          FStar_Syntax_Syntax.mk uu____2813
                                           in
                                        uu____2810
                                          (Some
                                             ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env e
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ
                                   in
                                ((let uu____2838 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  match uu____2838 with
                                  | true  ->
                                      let uu____2839 =
                                        FStar_Range.string_of_range
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____2840 =
                                        let uu____2841 =
                                          cres.FStar_Syntax_Syntax.comp ()
                                           in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Print.comp_to_string
                                          uu____2841
                                         in
                                      FStar_Util.print2
                                        "(%s) comp type = %s\n" uu____2839
                                        uu____2840
                                  | uu____2842 -> ());
                                 (let uu____2843 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e, cres, uu____2843))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2846;
                FStar_Syntax_Syntax.lbunivs = uu____2847;
                FStar_Syntax_Syntax.lbtyp = uu____2848;
                FStar_Syntax_Syntax.lbeff = uu____2849;
                FStar_Syntax_Syntax.lbdef = uu____2850;_}::[]),uu____2851)
           ->
           ((let uu____2866 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             match uu____2866 with
             | true  ->
                 let uu____2867 = FStar_Syntax_Print.term_to_string top  in
                 FStar_Util.print1 "%s\n" uu____2867
             | uu____2868 -> ());
            check_top_level_let env top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2869),uu____2870) ->
           check_inner_let env top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2880;
                FStar_Syntax_Syntax.lbunivs = uu____2881;
                FStar_Syntax_Syntax.lbtyp = uu____2882;
                FStar_Syntax_Syntax.lbeff = uu____2883;
                FStar_Syntax_Syntax.lbdef = uu____2884;_}::uu____2885),uu____2886)
           ->
           ((let uu____2902 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             match uu____2902 with
             | true  ->
                 let uu____2903 = FStar_Syntax_Print.term_to_string top  in
                 FStar_Util.print1 "%s\n" uu____2903
             | uu____2904 -> ());
            check_top_level_let_rec env top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____2905),uu____2906) ->
           check_inner_let_rec env top)

and tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env v dc e t =
        let uu____2950 = FStar_TypeChecker_Util.maybe_instantiate env e t  in
        match uu____2950 with
        | (e,t,implicits) ->
            let tc =
              let uu____2963 = FStar_TypeChecker_Env.should_verify env  in
              match uu____2963 with
              | true  -> FStar_Util.Inl t
              | uu____2966 ->
                  let uu____2967 =
                    let uu____2968 = FStar_Syntax_Syntax.mk_Total t  in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____2968
                     in
                  FStar_Util.Inr uu____2967
               in
            let is_data_ctor uu___79_2977 =
              match uu___79_2977 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____2980 -> false  in
            let uu____2982 =
              (is_data_ctor dc) &&
                (let uu____2983 =
                   FStar_TypeChecker_Env.is_datacon env
                     v.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____2983)
               in
            (match uu____2982 with
             | true  ->
                 let uu____2989 =
                   let uu____2990 =
                     let uu____2993 =
                       FStar_Util.format1
                         "Expected a data constructor; got %s"
                         (v.FStar_Syntax_Syntax.v).FStar_Ident.str
                        in
                     let uu____2996 = FStar_TypeChecker_Env.get_range env  in
                     (uu____2993, uu____2996)  in
                   FStar_Errors.Error uu____2990  in
                 Prims.raise uu____2989
             | uu____3000 -> value_check_expected_typ env e tc implicits)
         in
      let env = FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3007 =
            let uu____3008 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3008
             in
          failwith uu____3007
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3027 =
              let uu____3028 = FStar_Syntax_Subst.compress t1  in
              uu____3028.FStar_Syntax_Syntax.n  in
            match uu____3027 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3031 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3039 ->
                let imp =
                  ("uvar in term", env, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___92_3059 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___92_3059.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___92_3059.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___92_3059.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env  in
          let uu____3087 =
            let uu____3094 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____3094 with
            | None  ->
                let uu____3102 = FStar_Syntax_Util.type_u ()  in
                (match uu____3102 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard)  in
          (match uu____3087 with
           | (t,uu____3123,g0) ->
               let uu____3131 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env t
                  in
               (match uu____3131 with
                | (e,uu____3142,g1) ->
                    let uu____3150 =
                      let uu____3151 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____3151
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____3152 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e, uu____3150, uu____3152)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let t =
            match env.FStar_TypeChecker_Env.use_bv_sorts with
            | true  -> x.FStar_Syntax_Syntax.sort
            | uu____3159 -> FStar_TypeChecker_Env.lookup_bv env x  in
          let e =
            FStar_Syntax_Syntax.bv_to_name
              (let uu___93_3161 = x  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___93_3161.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___93_3161.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = t
               })
             in
          let uu____3162 = FStar_TypeChecker_Util.maybe_instantiate env e t
             in
          (match uu____3162 with
           | (e,t,implicits) ->
               let tc =
                 let uu____3175 = FStar_TypeChecker_Env.should_verify env  in
                 match uu____3175 with
                 | true  -> FStar_Util.Inl t
                 | uu____3178 ->
                     let uu____3179 =
                       let uu____3180 = FStar_Syntax_Syntax.mk_Total t  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3180
                        in
                     FStar_Util.Inr uu____3179
                  in
               value_check_expected_typ env e tc implicits)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3186;
             FStar_Syntax_Syntax.pos = uu____3187;
             FStar_Syntax_Syntax.vars = uu____3188;_},us)
          ->
          let us = FStar_List.map (tc_universe env) us  in
          let uu____3196 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3196 with
           | (us',t) ->
               ((match (FStar_List.length us) <> (FStar_List.length us') with
                 | true  ->
                     let uu____3213 =
                       let uu____3214 =
                         let uu____3217 = FStar_TypeChecker_Env.get_range env
                            in
                         ("Unexpected number of universe instantiations",
                           uu____3217)
                          in
                       FStar_Errors.Error uu____3214  in
                     Prims.raise uu____3213
                 | uu____3218 ->
                     FStar_List.iter2
                       (fun u'  ->
                          fun u  ->
                            match u' with
                            | FStar_Syntax_Syntax.U_unif u'' ->
                                FStar_Unionfind.change u'' (Some u)
                            | uu____3225 -> failwith "Impossible") us' us);
                (let fv' =
                   let uu___94_3227 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___95_3228 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___95_3228.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___95_3228.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___94_3227.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___94_3227.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 let e =
                   let uu____3242 =
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv'))
                       (Some (t.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3242 us  in
                 check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name
                   fv'.FStar_Syntax_Syntax.fv_qual e t)))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3254 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3254 with
           | (us,t) ->
               ((let uu____3267 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Range")
                    in
                 match uu____3267 with
                 | true  ->
                     let uu____3268 =
                       let uu____3269 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Syntax_Print.lid_to_string uu____3269  in
                     let uu____3270 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____3271 =
                       let uu____3272 =
                         let uu____3273 = FStar_Syntax_Syntax.lid_of_fv fv
                            in
                         FStar_Ident.range_of_lid uu____3273  in
                       FStar_Range.string_of_range uu____3272  in
                     let uu____3274 =
                       let uu____3275 =
                         let uu____3276 = FStar_Syntax_Syntax.lid_of_fv fv
                            in
                         FStar_Ident.range_of_lid uu____3276  in
                       FStar_Range.string_of_use_range uu____3275  in
                     let uu____3277 = FStar_Syntax_Print.term_to_string t  in
                     FStar_Util.print5
                       "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s"
                       uu____3268 uu____3270 uu____3271 uu____3274 uu____3277
                 | uu____3278 -> ());
                (let fv' =
                   let uu___96_3280 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___97_3281 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___97_3281.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___97_3281.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___96_3280.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___96_3280.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 let e =
                   let uu____3295 =
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv'))
                       (Some (t.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3295 us  in
                 check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name
                   fv'.FStar_Syntax_Syntax.fv_qual e t)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c  in
          let e =
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
              (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env e (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____3331 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3331 with
           | (bs,c) ->
               let env0 = env  in
               let uu____3340 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____3340 with
                | (env,uu____3348) ->
                    let uu____3351 = tc_binders env bs  in
                    (match uu____3351 with
                     | (bs,env,g,us) ->
                         let uu____3363 = tc_comp env c  in
                         (match uu____3363 with
                          | (c,uc,f) ->
                              let e =
                                let uu___98_3376 =
                                  FStar_Syntax_Util.arrow bs c  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___98_3376.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___98_3376.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___98_3376.FStar_Syntax_Syntax.vars)
                                }  in
                              (check_smt_pat env e bs c;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us)
                                   in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos
                                   in
                                let g =
                                  let uu____3397 =
                                    FStar_TypeChecker_Rel.close_guard bs f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3397
                                   in
                                value_check_expected_typ env0 e
                                  (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u = tc_universe env u  in
          let t =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
              None top.FStar_Syntax_Syntax.pos
             in
          let e =
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u))
              (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env e (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____3432 =
            let uu____3435 =
              let uu____3436 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____3436]  in
            FStar_Syntax_Subst.open_term uu____3435 phi  in
          (match uu____3432 with
           | (x,phi) ->
               let env0 = env  in
               let uu____3443 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____3443 with
                | (env,uu____3451) ->
                    let uu____3454 =
                      let uu____3461 = FStar_List.hd x  in
                      tc_binder env uu____3461  in
                    (match uu____3454 with
                     | (x,env,f1,u) ->
                         ((let uu____3478 =
                             FStar_TypeChecker_Env.debug env
                               FStar_Options.High
                              in
                           match uu____3478 with
                           | true  ->
                               let uu____3479 =
                                 FStar_Range.string_of_range
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____3480 =
                                 FStar_Syntax_Print.term_to_string phi  in
                               let uu____3481 =
                                 FStar_Syntax_Print.bv_to_string
                                   (Prims.fst x)
                                  in
                               FStar_Util.print3
                                 "(%s) Checking refinement formula %s; binder is %s\n"
                                 uu____3479 uu____3480 uu____3481
                           | uu____3482 -> ());
                          (let uu____3483 = FStar_Syntax_Util.type_u ()  in
                           match uu____3483 with
                           | (t_phi,uu____3490) ->
                               let uu____3491 =
                                 tc_check_tot_or_gtot_term env phi t_phi  in
                               (match uu____3491 with
                                | (phi,uu____3499,f2) ->
                                    let e =
                                      let uu___99_3504 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x) phi
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___99_3504.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___99_3504.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___99_3504.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____3523 =
                                        FStar_TypeChecker_Rel.close_guard 
                                          [x] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3523
                                       in
                                    value_check_expected_typ env0 e
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3532) ->
          let bs = FStar_TypeChecker_Util.maybe_add_implicit_binders env bs
             in
          ((let uu____3557 =
              FStar_TypeChecker_Env.debug env FStar_Options.Low  in
            match uu____3557 with
            | true  ->
                let uu____3558 =
                  FStar_Syntax_Print.term_to_string
                    (let uu___100_3559 = top  in
                     {
                       FStar_Syntax_Syntax.n =
                         (FStar_Syntax_Syntax.Tm_abs (bs, body, None));
                       FStar_Syntax_Syntax.tk =
                         (uu___100_3559.FStar_Syntax_Syntax.tk);
                       FStar_Syntax_Syntax.pos =
                         (uu___100_3559.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___100_3559.FStar_Syntax_Syntax.vars)
                     })
                   in
                FStar_Util.print1 "Abstraction is: %s\n" uu____3558
            | uu____3577 -> ());
           (let uu____3578 = FStar_Syntax_Subst.open_term bs body  in
            match uu____3578 with | (bs,body) -> tc_abs env top bs body))
      | uu____3586 ->
          let uu____3587 =
            let uu____3588 = FStar_Syntax_Print.term_to_string top  in
            let uu____3589 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3588
              uu____3589
             in
          failwith uu____3587

and tc_constant :
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3595 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3596,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3602,Some uu____3603) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3611 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3615 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3616 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3617 ->
          FStar_TypeChecker_Common.t_range
      | uu____3618 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____3629) ->
          let uu____3636 = FStar_Syntax_Util.type_u ()  in
          (match uu____3636 with
           | (k,u) ->
               let uu____3644 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3644 with
                | (t,uu____3652,g) ->
                    let uu____3654 = FStar_Syntax_Syntax.mk_Total' t (Some u)
                       in
                    (uu____3654, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3656) ->
          let uu____3663 = FStar_Syntax_Util.type_u ()  in
          (match uu____3663 with
           | (k,u) ->
               let uu____3671 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3671 with
                | (t,uu____3679,g) ->
                    let uu____3681 =
                      FStar_Syntax_Syntax.mk_GTotal' t (Some u)  in
                    (uu____3681, u, g)))
      | FStar_Syntax_Syntax.Comp c ->
          let head =
            FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant None
             in
          let head =
            match c.FStar_Syntax_Syntax.comp_univs with
            | [] -> head
            | us ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_uinst (head, us))) None
                  c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____3697 =
              let uu____3698 =
                let uu____3699 =
                  FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ
                   in
                uu____3699 :: (c.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head uu____3698  in
            uu____3697 None
              (c.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____3704 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____3704 with
           | (tc,uu____3712,f) ->
               let uu____3714 = FStar_Syntax_Util.head_and_args tc  in
               (match uu____3714 with
                | (head,args) ->
                    let comp_univs =
                      let uu____3744 =
                        let uu____3745 = FStar_Syntax_Subst.compress head  in
                        uu____3745.FStar_Syntax_Syntax.n  in
                      match uu____3744 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3748,us) -> us
                      | uu____3754 -> []  in
                    let uu____3755 = FStar_Syntax_Util.head_and_args tc  in
                    (match uu____3755 with
                     | (uu____3768,args) ->
                         let uu____3784 =
                           let uu____3796 = FStar_List.hd args  in
                           let uu____3805 = FStar_List.tl args  in
                           (uu____3796, uu____3805)  in
                         (match uu____3784 with
                          | (res,args) ->
                              let uu____3847 =
                                let uu____3852 =
                                  FStar_All.pipe_right
                                    c.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___80_3862  ->
                                          match uu___80_3862 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____3868 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____3868 with
                                               | (env,uu____3875) ->
                                                   let uu____3878 =
                                                     tc_tot_or_gtot_term env
                                                       e
                                                      in
                                                   (match uu____3878 with
                                                    | (e,uu____3885,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e), g)))
                                          | f ->
                                              (f,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____3852
                                  FStar_List.unzip
                                 in
                              (match uu____3847 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (Prims.fst res)
                                      in
                                   let c =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___101_3908 = c  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___101_3908.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (Prims.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___101_3908.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____3912 =
                                       FStar_TypeChecker_Util.effect_repr env
                                         c u
                                        in
                                     match uu____3912 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____3915 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c, u_c, uu____3915))))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u =
        let u = FStar_Syntax_Subst.compress_univ u  in
        match u with
        | FStar_Syntax_Syntax.U_bvar uu____3923 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  -> u
        | FStar_Syntax_Syntax.U_succ u ->
            let uu____3926 = aux u  in FStar_Syntax_Syntax.U_succ uu____3926
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3929 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3929
        | FStar_Syntax_Syntax.U_name x -> u  in
      match env.FStar_TypeChecker_Env.lax_universes with
      | true  -> FStar_Syntax_Syntax.U_zero
      | uu____3932 ->
          (match u with
           | FStar_Syntax_Syntax.U_unknown  ->
               let uu____3933 = FStar_Syntax_Util.type_u ()  in
               FStar_All.pipe_right uu____3933 Prims.snd
           | uu____3938 -> aux u)

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
            let uu____3959 =
              let uu____3960 =
                let uu____3963 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top
                   in
                (uu____3963, (top.FStar_Syntax_Syntax.pos))  in
              FStar_Errors.Error uu____3960  in
            Prims.raise uu____3959  in
          let check_binders env bs bs_expected =
            let rec aux uu____4017 bs bs_expected =
              match uu____4017 with
              | (env,out,g,subst) ->
                  (match (bs, bs_expected) with
                   | ([],[]) -> (env, (FStar_List.rev out), None, g, subst)
                   | ((hd,imp)::bs,(hd_expected,imp')::bs_expected) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             let uu____4114 =
                               let uu____4115 =
                                 let uu____4118 =
                                   let uu____4119 =
                                     FStar_Syntax_Print.bv_to_string hd  in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4119
                                    in
                                 let uu____4120 =
                                   FStar_Syntax_Syntax.range_of_bv hd  in
                                 (uu____4118, uu____4120)  in
                               FStar_Errors.Error uu____4115  in
                             Prims.raise uu____4114
                         | uu____4121 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____4125 =
                           let uu____4128 =
                             let uu____4129 =
                               FStar_Syntax_Util.unmeta
                                 hd.FStar_Syntax_Syntax.sort
                                in
                             uu____4129.FStar_Syntax_Syntax.n  in
                           match uu____4128 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4134 ->
                               ((let uu____4136 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.High
                                    in
                                 match uu____4136 with
                                 | true  ->
                                     let uu____4137 =
                                       FStar_Syntax_Print.bv_to_string hd  in
                                     FStar_Util.print1 "Checking binder %s\n"
                                       uu____4137
                                 | uu____4138 -> ());
                                (let uu____4139 =
                                   tc_tot_or_gtot_term env
                                     hd.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____4139 with
                                 | (t,uu____4146,g1) ->
                                     let g2 =
                                       let uu____4149 =
                                         FStar_TypeChecker_Env.get_range env
                                          in
                                       let uu____4150 =
                                         FStar_TypeChecker_Rel.teq env t
                                           expected_t
                                          in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4149
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4150
                                        in
                                     let g =
                                       let uu____4152 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4152
                                        in
                                     (t, g)))
                            in
                         match uu____4125 with
                         | (t,g) ->
                             let hd =
                               let uu___102_4168 = hd  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___102_4168.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___102_4168.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env = push_binding env b  in
                             let subst =
                               let uu____4177 =
                                 FStar_Syntax_Syntax.bv_to_name hd  in
                               maybe_extend_subst subst b_expected uu____4177
                                in
                             aux (env, (b :: out), g, subst) bs bs_expected))
                   | (rest,[]) ->
                       (env, (FStar_List.rev out),
                         (Some (FStar_Util.Inl rest)), g, subst)
                   | ([],rest) ->
                       (env, (FStar_List.rev out),
                         (Some (FStar_Util.Inr rest)), g, subst))
               in
            aux (env, [], FStar_TypeChecker_Rel.trivial_guard, []) bs
              bs_expected
             in
          let rec expected_function_typ env t0 body =
            match t0 with
            | None  ->
                ((match env.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____4273 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4277 = tc_binders env bs  in
                  match uu____4277 with
                  | (bs,envbody,g,uu____4296) ->
                      let uu____4297 =
                        let uu____4302 =
                          let uu____4303 = FStar_Syntax_Subst.compress body
                             in
                          uu____4303.FStar_Syntax_Syntax.n  in
                        match uu____4302 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,FStar_Util.Inr c,uu____4312) ->
                            let uu____4331 = tc_comp envbody c  in
                            (match uu____4331 with
                             | (c,uu____4340,g') ->
                                 let uu____4342 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((Some c), body, uu____4342))
                        | uu____4344 -> (None, body, g)  in
                      (match uu____4297 with
                       | (copt,body,g) ->
                           (None, bs, [], copt, envbody, body, g))))
            | Some t ->
                let t = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm t =
                  let uu____4394 =
                    let uu____4395 = FStar_Syntax_Subst.compress t  in
                    uu____4395.FStar_Syntax_Syntax.n  in
                  match uu____4394 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4426 -> failwith "Impossible");
                       (let uu____4430 = tc_binders env bs  in
                        match uu____4430 with
                        | (bs,envbody,g,uu____4450) ->
                            let uu____4451 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____4451 with
                             | (envbody,uu____4468) ->
                                 ((Some (t, true)), bs, [], None, envbody,
                                   body, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4479) ->
                      let uu____4484 =
                        as_function_typ norm b.FStar_Syntax_Syntax.sort  in
                      (match uu____4484 with
                       | (uu____4509,bs,bs',copt,env,body,g) ->
                           ((Some (t, false)), bs, bs', copt, env, body, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4545 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____4545 with
                       | (bs_expected,c_expected) ->
                           let check_actuals_against_formals env bs
                             bs_expected =
                             let rec handle_more uu____4606 c_expected =
                               match uu____4606 with
                               | (env,bs,more,guard,subst) ->
                                   (match more with
                                    | None  ->
                                        let uu____4667 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected
                                           in
                                        (env, bs, guard, uu____4667)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____4684 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____4684
                                           in
                                        let uu____4685 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c
                                           in
                                        (env, bs, guard, uu____4685)
                                    | Some (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected
                                           in
                                        (match FStar_Syntax_Util.is_named_tot
                                                 c
                                         with
                                         | true  ->
                                             let t =
                                               unfold_whnf env
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                in
                                             (match t.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (bs_expected,c_expected) ->
                                                  let uu____4726 =
                                                    check_binders env more_bs
                                                      bs_expected
                                                     in
                                                  (match uu____4726 with
                                                   | (env,bs',more,guard',subst)
                                                       ->
                                                       let uu____4753 =
                                                         let uu____4769 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard guard'
                                                            in
                                                         (env,
                                                           (FStar_List.append
                                                              bs bs'), more,
                                                           uu____4769, subst)
                                                          in
                                                       handle_more uu____4753
                                                         c_expected)
                                              | uu____4778 ->
                                                  let uu____4779 =
                                                    let uu____4780 =
                                                      FStar_Syntax_Print.term_to_string
                                                        t
                                                       in
                                                    FStar_Util.format1
                                                      "More arguments than annotated type (%s)"
                                                      uu____4780
                                                     in
                                                  fail uu____4779 t)
                                         | uu____4788 ->
                                             fail
                                               "Function definition takes more arguments than expected from its annotated type"
                                               t))
                                in
                             let uu____4796 =
                               check_binders env bs bs_expected  in
                             handle_more uu____4796 c_expected  in
                           let mk_letrec_env envbody bs c =
                             let letrecs = guard_letrecs envbody bs c  in
                             let envbody =
                               let uu___103_4834 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___103_4834.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___103_4834.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___103_4834.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___103_4834.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___103_4834.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___103_4834.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___103_4834.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___103_4834.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___103_4834.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___103_4834.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___103_4834.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___103_4834.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___103_4834.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___103_4834.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___103_4834.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___103_4834.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___103_4834.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___103_4834.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___103_4834.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___103_4834.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___103_4834.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___103_4834.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___103_4834.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____4848  ->
                                     fun uu____4849  ->
                                       match (uu____4848, uu____4849) with
                                       | ((env,letrec_binders),(l,t)) ->
                                           let uu____4874 =
                                             let uu____4878 =
                                               let uu____4879 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4879 Prims.fst
                                                in
                                             tc_term uu____4878 t  in
                                           (match uu____4874 with
                                            | (t,uu____4891,uu____4892) ->
                                                let env =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env l ([], t)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____4899 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___104_4900
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___104_4900.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___104_4900.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t
                                                           })
                                                         in
                                                      uu____4899 ::
                                                        letrec_binders
                                                  | uu____4901 ->
                                                      letrec_binders
                                                   in
                                                (env, lb))) (envbody, []))
                              in
                           let uu____4904 =
                             check_actuals_against_formals env bs bs_expected
                              in
                           (match uu____4904 with
                            | (envbody,bs,g,c) ->
                                let uu____4934 =
                                  let uu____4938 =
                                    FStar_TypeChecker_Env.should_verify env
                                     in
                                  match uu____4938 with
                                  | true  -> mk_letrec_env envbody bs c
                                  | uu____4942 -> (envbody, [])  in
                                (match uu____4934 with
                                 | (envbody,letrecs) ->
                                     let envbody =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((Some (t, false)), bs, letrecs,
                                       (Some c), envbody, body, g))))
                  | uu____4971 ->
                      (match Prims.op_Negation norm with
                       | true  ->
                           let uu____4984 = unfold_whnf env t  in
                           as_function_typ true uu____4984
                       | uu____4985 ->
                           let uu____4986 =
                             expected_function_typ env None body  in
                           (match uu____4986 with
                            | (uu____5010,bs,uu____5012,c_opt,envbody,body,g)
                                ->
                                ((Some (t, false)), bs, [], c_opt, envbody,
                                  body, g)))
                   in
                as_function_typ false t
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____5033 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____5033 with
          | (env,topt) ->
              ((let uu____5045 =
                  FStar_TypeChecker_Env.debug env FStar_Options.High  in
                match uu____5045 with
                | true  ->
                    let uu____5046 =
                      match topt with
                      | None  -> "None"
                      | Some t -> FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                      uu____5046
                      (match env.FStar_TypeChecker_Env.top_level with
                       | true  -> "true"
                       | uu____5048 -> "false")
                | uu____5049 -> ());
               (let uu____5050 = expected_function_typ env topt body  in
                match uu____5050 with
                | (tfun_opt,bs,letrec_binders,c_opt,envbody,body,g) ->
                    let uu____5080 =
                      tc_term
                        (let uu___105_5084 = envbody  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___105_5084.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___105_5084.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___105_5084.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___105_5084.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___105_5084.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___105_5084.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___105_5084.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___105_5084.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___105_5084.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___105_5084.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___105_5084.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___105_5084.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___105_5084.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___105_5084.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___105_5084.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___105_5084.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___105_5084.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___105_5084.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___105_5084.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___105_5084.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___105_5084.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___105_5084.FStar_TypeChecker_Env.qname_and_index)
                         }) body
                       in
                    (match uu____5080 with
                     | (body,cbody,guard_body) ->
                         let guard_body =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         ((let uu____5093 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Implicits")
                              in
                           match uu____5093 with
                           | true  ->
                               let uu____5094 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length
                                      guard_body.FStar_TypeChecker_Env.implicits)
                                  in
                               let uu____5103 =
                                 let uu____5104 =
                                   cbody.FStar_Syntax_Syntax.comp ()  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Print.comp_to_string
                                   uu____5104
                                  in
                               FStar_Util.print2
                                 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                                 uu____5094 uu____5103
                           | uu____5105 -> ());
                          (let uu____5106 =
                             let uu____5110 =
                               let uu____5113 =
                                 cbody.FStar_Syntax_Syntax.comp ()  in
                               (body, uu____5113)  in
                             check_expected_effect
                               (let uu___106_5118 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___106_5118.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___106_5118.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___106_5118.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___106_5118.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___106_5118.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___106_5118.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___106_5118.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___106_5118.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___106_5118.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___106_5118.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___106_5118.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___106_5118.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___106_5118.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___106_5118.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___106_5118.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___106_5118.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___106_5118.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___106_5118.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___106_5118.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___106_5118.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___106_5118.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___106_5118.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___106_5118.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5110
                              in
                           match uu____5106 with
                           | (body,cbody,guard) ->
                               let guard =
                                 FStar_TypeChecker_Rel.conj_guard guard_body
                                   guard
                                  in
                               let guard =
                                 let uu____5127 =
                                   env.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5128 =
                                        FStar_TypeChecker_Env.should_verify
                                          env
                                         in
                                      Prims.op_Negation uu____5128)
                                    in
                                 match uu____5127 with
                                 | true  ->
                                     let uu____5129 =
                                       FStar_TypeChecker_Rel.conj_guard g
                                         guard
                                        in
                                     FStar_TypeChecker_Rel.discharge_guard
                                       envbody uu____5129
                                 | uu____5130 ->
                                     let guard =
                                       let uu____5132 =
                                         FStar_TypeChecker_Rel.conj_guard g
                                           guard
                                          in
                                       FStar_TypeChecker_Rel.close_guard
                                         (FStar_List.append bs letrec_binders)
                                         uu____5132
                                        in
                                     guard
                                  in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs cbody  in
                               let e =
                                 let uu____5139 =
                                   let uu____5146 =
                                     let uu____5152 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     FStar_All.pipe_right uu____5152
                                       (fun _0_29  -> FStar_Util.Inl _0_29)
                                      in
                                   Some uu____5146  in
                                 FStar_Syntax_Util.abs bs body uu____5139  in
                               let uu____5166 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t = FStar_Syntax_Subst.compress t
                                        in
                                     (match t.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5181 -> (e, t, guard)
                                      | uu____5189 ->
                                          let uu____5190 =
                                            match use_teq with
                                            | true  ->
                                                let uu____5195 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env t tfun_computed
                                                   in
                                                (e, uu____5195)
                                            | uu____5196 ->
                                                FStar_TypeChecker_Util.check_and_ascribe
                                                  env e tfun_computed t
                                             in
                                          (match uu____5190 with
                                           | (e,guard') ->
                                               let uu____5202 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard guard'
                                                  in
                                               (e, t, uu____5202)))
                                 | None  -> (e, tfun_computed, guard)  in
                               (match uu____5166 with
                                | (e,tfun,guard) ->
                                    let c =
                                      match env.FStar_TypeChecker_Env.top_level
                                      with
                                      | true  ->
                                          FStar_Syntax_Syntax.mk_Total tfun
                                      | uu____5214 ->
                                          FStar_TypeChecker_Util.return_value
                                            env tfun e
                                       in
                                    let uu____5215 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env e
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard
                                       in
                                    (match uu____5215 with
                                     | (c,g) -> (e, c, g))))))))

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
    fun head  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = chead.FStar_Syntax_Syntax.res_typ  in
              (let uu____5251 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               match uu____5251 with
               | true  ->
                   let uu____5252 =
                     FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos
                      in
                   let uu____5253 = FStar_Syntax_Print.term_to_string thead
                      in
                   FStar_Util.print2 "(%s) Type of head is %s\n" uu____5252
                     uu____5253
               | uu____5254 -> ());
              (let monadic_application uu____5295 subst arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____5295 with
                 | (head,chead,ghead,cres) ->
                     let rt =
                       check_no_escape (Some head) env fvs
                         cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres =
                       let uu___107_5336 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___107_5336.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___107_5336.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___107_5336.FStar_Syntax_Syntax.comp)
                       }  in
                     let uu____5337 =
                       match bs with
                       | [] ->
                           let cres =
                             FStar_TypeChecker_Util.subst_lcomp subst cres
                              in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead guard  in
                           let refine_with_equality =
                             (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres)
                               &&
                               (FStar_All.pipe_right arg_comps_rev
                                  (FStar_Util.for_some
                                     (fun uu___81_5364  ->
                                        match uu___81_5364 with
                                        | (uu____5373,uu____5374,FStar_Util.Inl
                                           uu____5375) -> false
                                        | (uu____5386,uu____5387,FStar_Util.Inr
                                           c) ->
                                            let uu____5397 =
                                              FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                c
                                               in
                                            Prims.op_Negation uu____5397)))
                              in
                           let cres =
                             match refine_with_equality with
                             | true  ->
                                 let uu____5399 =
                                   (FStar_Syntax_Syntax.mk_Tm_app head
                                      (FStar_List.rev arg_rets))
                                     (Some
                                        ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                     r
                                    in
                                 FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                   env uu____5399 cres
                             | uu____5408 ->
                                 ((let uu____5410 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.Low
                                      in
                                   match uu____5410 with
                                   | true  ->
                                       let uu____5411 =
                                         FStar_Syntax_Print.term_to_string
                                           head
                                          in
                                       let uu____5412 =
                                         FStar_Syntax_Print.lcomp_to_string
                                           cres
                                          in
                                       let uu____5413 =
                                         FStar_TypeChecker_Rel.guard_to_string
                                           env g
                                          in
                                       FStar_Util.print3
                                         "Not refining result: f=%s; cres=%s; guard=%s\n"
                                         uu____5411 uu____5412 uu____5413
                                   | uu____5414 -> ());
                                  cres)
                              in
                           (cres, g)
                       | uu____5415 ->
                           let g =
                             let uu____5420 =
                               FStar_TypeChecker_Rel.conj_guard ghead guard
                                in
                             FStar_All.pipe_right uu____5420
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____5421 =
                             let uu____5422 =
                               let uu____5425 =
                                 let uu____5426 =
                                   let uu____5427 =
                                     cres.FStar_Syntax_Syntax.comp ()  in
                                   FStar_Syntax_Util.arrow bs uu____5427  in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst)
                                   uu____5426
                                  in
                               FStar_Syntax_Syntax.mk_Total uu____5425  in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5422
                              in
                           (uu____5421, g)
                        in
                     (match uu____5337 with
                      | (cres,guard) ->
                          ((let uu____5438 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            match uu____5438 with
                            | true  ->
                                let uu____5439 =
                                  FStar_Syntax_Print.lcomp_to_string cres  in
                                FStar_Util.print1
                                  "\t Type of result cres is %s\n" uu____5439
                            | uu____5440 -> ());
                           (let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____5455  ->
                                     match uu____5455 with
                                     | ((e,q),x,c) ->
                                         (match c with
                                          | FStar_Util.Inl (eff_name,arg_typ)
                                              -> out_c
                                          | FStar_Util.Inr c ->
                                              FStar_TypeChecker_Util.bind
                                                e.FStar_Syntax_Syntax.pos env
                                                None c (x, out_c))) cres
                                arg_comps_rev
                               in
                            let comp =
                              FStar_TypeChecker_Util.bind
                                head.FStar_Syntax_Syntax.pos env None chead
                                (None, comp)
                               in
                            let shortcuts_evaluation_order =
                              let uu____5501 =
                                let uu____5502 =
                                  FStar_Syntax_Subst.compress head  in
                                uu____5502.FStar_Syntax_Syntax.n  in
                              match uu____5501 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____5506 -> false  in
                            let app =
                              match shortcuts_evaluation_order with
                              | true  ->
                                  let args =
                                    FStar_List.fold_left
                                      (fun args  ->
                                         fun uu____5520  ->
                                           match uu____5520 with
                                           | (arg,uu____5532,uu____5533) ->
                                               arg :: args) [] arg_comps_rev
                                     in
                                  let app =
                                    (FStar_Syntax_Syntax.mk_Tm_app head args)
                                      (Some
                                         ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                      r
                                     in
                                  let app =
                                    FStar_TypeChecker_Util.maybe_lift env app
                                      cres.FStar_Syntax_Syntax.eff_name
                                      comp.FStar_Syntax_Syntax.eff_name
                                      comp.FStar_Syntax_Syntax.res_typ
                                     in
                                  FStar_TypeChecker_Util.maybe_monadic env
                                    app comp.FStar_Syntax_Syntax.eff_name
                                    comp.FStar_Syntax_Syntax.res_typ
                              | uu____5552 ->
                                  let uu____5553 =
                                    let map_fun uu____5592 =
                                      match uu____5592 with
                                      | ((e,q),uu____5616,c0) ->
                                          (match c0 with
                                           | FStar_Util.Inl uu____5641 ->
                                               (None, (e, q))
                                           | FStar_Util.Inr c when
                                               FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 c
                                               -> (None, (e, q))
                                           | FStar_Util.Inr c ->
                                               let x =
                                                 FStar_Syntax_Syntax.new_bv
                                                   None
                                                   c.FStar_Syntax_Syntax.res_typ
                                                  in
                                               let e =
                                                 FStar_TypeChecker_Util.maybe_lift
                                                   env e
                                                   c.FStar_Syntax_Syntax.eff_name
                                                   comp.FStar_Syntax_Syntax.eff_name
                                                   c.FStar_Syntax_Syntax.res_typ
                                                  in
                                               let uu____5684 =
                                                 let uu____5687 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x
                                                    in
                                                 (uu____5687, q)  in
                                               ((Some
                                                   (x,
                                                     (c.FStar_Syntax_Syntax.eff_name),
                                                     (c.FStar_Syntax_Syntax.res_typ),
                                                     e)), uu____5684))
                                       in
                                    let uu____5705 =
                                      let uu____5719 =
                                        let uu____5732 =
                                          let uu____5744 =
                                            let uu____5753 =
                                              FStar_Syntax_Syntax.as_arg head
                                               in
                                            (uu____5753, None,
                                              (FStar_Util.Inr chead))
                                             in
                                          uu____5744 :: arg_comps_rev  in
                                        FStar_List.map map_fun uu____5732  in
                                      FStar_All.pipe_left FStar_List.split
                                        uu____5719
                                       in
                                    match uu____5705 with
                                    | (lifted_args,reverse_args) ->
                                        let uu____5862 =
                                          let uu____5863 =
                                            FStar_List.hd reverse_args  in
                                          Prims.fst uu____5863  in
                                        let uu____5868 =
                                          let uu____5872 =
                                            FStar_List.tl reverse_args  in
                                          FStar_List.rev uu____5872  in
                                        (lifted_args, uu____5862, uu____5868)
                                     in
                                  (match uu____5553 with
                                   | (lifted_args,head,args) ->
                                       let app =
                                         (FStar_Syntax_Syntax.mk_Tm_app head
                                            args)
                                           (Some
                                              ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                           r
                                          in
                                       let app =
                                         FStar_TypeChecker_Util.maybe_lift
                                           env app
                                           cres.FStar_Syntax_Syntax.eff_name
                                           comp.FStar_Syntax_Syntax.eff_name
                                           comp.FStar_Syntax_Syntax.res_typ
                                          in
                                       let app =
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env app
                                           comp.FStar_Syntax_Syntax.eff_name
                                           comp.FStar_Syntax_Syntax.res_typ
                                          in
                                       let bind_lifted_args e uu___82_5940 =
                                         match uu___82_5940 with
                                         | None  -> e
                                         | Some (x,m,t,e1) ->
                                             let lb =
                                               FStar_Syntax_Util.mk_letbinding
                                                 (FStar_Util.Inl x) [] t m e1
                                                in
                                             let letbinding =
                                               let uu____5982 =
                                                 let uu____5985 =
                                                   let uu____5986 =
                                                     let uu____5994 =
                                                       let uu____5995 =
                                                         let uu____5996 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             x
                                                            in
                                                         [uu____5996]  in
                                                       FStar_Syntax_Subst.close
                                                         uu____5995 e
                                                        in
                                                     ((false, [lb]),
                                                       uu____5994)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_let
                                                     uu____5986
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____5985
                                                  in
                                               uu____5982 None
                                                 e.FStar_Syntax_Syntax.pos
                                                in
                                             (FStar_Syntax_Syntax.mk
                                                (FStar_Syntax_Syntax.Tm_meta
                                                   (letbinding,
                                                     (FStar_Syntax_Syntax.Meta_monadic
                                                        (m,
                                                          (comp.FStar_Syntax_Syntax.res_typ))))))
                                               None e.FStar_Syntax_Syntax.pos
                                          in
                                       FStar_List.fold_left bind_lifted_args
                                         app lifted_args)
                               in
                            let uu____6030 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp guard
                               in
                            match uu____6030 with
                            | (comp,g) -> (app, comp, g))))
                  in
               let rec tc_args head_info uu____6088 bs args =
                 match uu____6088 with
                 | (subst,outargs,arg_rets,g,fvs) ->
                     (match (bs, args) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6183))::rest,
                         (uu____6185,None )::uu____6186) ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t = check_no_escape (Some head) env fvs t  in
                          let uu____6223 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head.FStar_Syntax_Syntax.pos env t
                             in
                          (match uu____6223 with
                           | (varg,uu____6234,implicits) ->
                               let subst = (FStar_Syntax_Syntax.NT (x, varg))
                                 :: subst  in
                               let arg =
                                 let uu____6247 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____6247)  in
                               let uu____6248 =
                                 let uu____6270 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t))) :: outargs), (arg ::
                                   arg_rets), uu____6270, fvs)
                                  in
                               tc_args head_info uu____6248 rest args)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____6361 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x =
                              let uu___108_6368 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___108_6368.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___108_6368.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____6370 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             match uu____6370 with
                             | true  ->
                                 let uu____6371 =
                                   FStar_Syntax_Print.term_to_string targ  in
                                 FStar_Util.print1
                                   "\tType of arg (after subst) = %s\n"
                                   uu____6371
                             | uu____6372 -> ());
                            (let targ =
                               check_no_escape (Some head) env fvs targ  in
                             let env =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ
                                in
                             let env =
                               let uu___109_6376 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___109_6376.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___109_6376.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___109_6376.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___109_6376.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___109_6376.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___109_6376.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___109_6376.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___109_6376.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___109_6376.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___109_6376.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___109_6376.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___109_6376.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___109_6376.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___109_6376.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___109_6376.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___109_6376.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___109_6376.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___109_6376.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___109_6376.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___109_6376.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___109_6376.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___109_6376.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___109_6376.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             (let uu____6378 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.High
                                 in
                              match uu____6378 with
                              | true  ->
                                  let uu____6379 =
                                    FStar_Syntax_Print.tag_of_term e  in
                                  let uu____6380 =
                                    FStar_Syntax_Print.term_to_string e  in
                                  let uu____6381 =
                                    FStar_Syntax_Print.term_to_string targ
                                     in
                                  FStar_Util.print3
                                    "Checking arg (%s) %s at type %s\n"
                                    uu____6379 uu____6380 uu____6381
                              | uu____6382 -> ());
                             (let uu____6383 = tc_term env e  in
                              match uu____6383 with
                              | (e,c,g_e) ->
                                  let g =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e, aq)  in
                                  let uu____6399 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c
                                     in
                                  (match uu____6399 with
                                   | true  ->
                                       let subst =
                                         let uu____6404 = FStar_List.hd bs
                                            in
                                         maybe_extend_subst subst uu____6404
                                           e
                                          in
                                       tc_args head_info
                                         (subst,
                                           ((arg, None,
                                              (FStar_Util.Inl
                                                 ((c.FStar_Syntax_Syntax.eff_name),
                                                   (c.FStar_Syntax_Syntax.res_typ))))
                                           :: outargs), (arg :: arg_rets), g,
                                           fvs) rest rest'
                                   | uu____6459 ->
                                       let uu____6460 =
                                         FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                           env c.FStar_Syntax_Syntax.eff_name
                                          in
                                       (match uu____6460 with
                                        | true  ->
                                            let subst =
                                              let uu____6465 =
                                                FStar_List.hd bs  in
                                              maybe_extend_subst subst
                                                uu____6465 e
                                               in
                                            tc_args head_info
                                              (subst,
                                                ((arg, (Some x),
                                                   (FStar_Util.Inr c)) ::
                                                outargs), (arg :: arg_rets),
                                                g, fvs) rest rest'
                                        | uu____6510 ->
                                            let uu____6511 =
                                              let uu____6512 =
                                                FStar_List.hd bs  in
                                              FStar_Syntax_Syntax.is_null_binder
                                                uu____6512
                                               in
                                            (match uu____6511 with
                                             | true  ->
                                                 let newx =
                                                   FStar_Syntax_Syntax.new_bv
                                                     (Some
                                                        (e.FStar_Syntax_Syntax.pos))
                                                     c.FStar_Syntax_Syntax.res_typ
                                                    in
                                                 let arg' =
                                                   let uu____6521 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       newx
                                                      in
                                                   FStar_All.pipe_left
                                                     FStar_Syntax_Syntax.as_arg
                                                     uu____6521
                                                    in
                                                 tc_args head_info
                                                   (subst,
                                                     ((arg, (Some newx),
                                                        (FStar_Util.Inr c))
                                                     :: outargs), (arg' ::
                                                     arg_rets), g, fvs) rest
                                                   rest'
                                             | uu____6558 ->
                                                 let uu____6559 =
                                                   let uu____6581 =
                                                     let uu____6583 =
                                                       let uu____6584 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.as_arg
                                                         uu____6584
                                                        in
                                                     uu____6583 :: arg_rets
                                                      in
                                                   (subst,
                                                     ((arg, (Some x),
                                                        (FStar_Util.Inr c))
                                                     :: outargs), uu____6581,
                                                     g, (x :: fvs))
                                                    in
                                                 tc_args head_info uu____6559
                                                   rest rest')))))))
                      | (uu____6621,[]) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6642) ->
                          let uu____6672 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs []
                             in
                          (match uu____6672 with
                           | (head,chead,ghead) ->
                               let rec aux norm tres =
                                 let tres =
                                   let uu____6695 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____6695
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,cres') ->
                                     let uu____6711 =
                                       FStar_Syntax_Subst.open_comp bs cres'
                                        in
                                     (match uu____6711 with
                                      | (bs,cres') ->
                                          let head_info =
                                            (head, chead, ghead,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'))
                                             in
                                          ((let uu____6725 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            match uu____6725 with
                                            | true  ->
                                                let uu____6726 =
                                                  FStar_Range.string_of_range
                                                    tres.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Util.print1
                                                  "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                  uu____6726
                                            | uu____6727 -> ());
                                           tc_args head_info
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs args))
                                 | uu____6756 when Prims.op_Negation norm ->
                                     let uu____6757 = unfold_whnf env tres
                                        in
                                     aux true uu____6757
                                 | uu____6758 ->
                                     let uu____6759 =
                                       let uu____6760 =
                                         let uu____6763 =
                                           let uu____6764 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead
                                              in
                                           let uu____6765 =
                                             FStar_Util.string_of_int n_args
                                              in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6764 uu____6765
                                            in
                                         let uu____6769 =
                                           FStar_Syntax_Syntax.argpos arg  in
                                         (uu____6763, uu____6769)  in
                                       FStar_Errors.Error uu____6760  in
                                     Prims.raise uu____6759
                                  in
                               aux false chead.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app norm tf =
                 let uu____6785 =
                   let uu____6786 = FStar_Syntax_Util.unrefine tf  in
                   uu____6786.FStar_Syntax_Syntax.n  in
                 match uu____6785 with
                 | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_)
                     ->
                     let rec tc_args env args =
                       match args with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl ->
                           let uu____6862 = tc_term env e  in
                           (match uu____6862 with
                            | (e,c,g_e) ->
                                let uu____6875 = tc_args env tl  in
                                (match uu____6875 with
                                 | (args,comps,g_rest) ->
                                     let uu____6897 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e, imp) :: args),
                                       (((e.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____6897)))
                        in
                     let uu____6908 = tc_args env args  in
                     (match uu____6908 with
                      | (args,comps,g_args) ->
                          let bs =
                            let uu____6930 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____6950  ->
                                      match uu____6950 with
                                      | (uu____6958,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____6930
                             in
                          let ml_or_tot t r =
                            let uu____6974 = FStar_Options.ml_ish ()  in
                            match uu____6974 with
                            | true  -> FStar_Syntax_Util.ml_comp t r
                            | uu____6975 -> FStar_Syntax_Syntax.mk_Total t
                             in
                          let cres =
                            let uu____6977 =
                              let uu____6980 =
                                let uu____6981 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____6981 Prims.fst  in
                              FStar_TypeChecker_Util.new_uvar env uu____6980
                               in
                            ml_or_tot uu____6977 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____6990 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            match uu____6990 with
                            | true  ->
                                let uu____6991 =
                                  FStar_Syntax_Print.term_to_string head  in
                                let uu____6992 =
                                  FStar_Syntax_Print.term_to_string tf  in
                                let uu____6993 =
                                  FStar_Syntax_Print.term_to_string bs_cres
                                   in
                                FStar_Util.print3
                                  "Forcing the type of %s from %s to %s\n"
                                  uu____6991 uu____6992 uu____6993
                            | uu____6994 -> ());
                           (let uu____6996 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____6996);
                           (let comp =
                              let uu____6998 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____7003  ->
                                   fun out  ->
                                     match uu____7003 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____6998
                               in
                            let uu____7012 =
                              (FStar_Syntax_Syntax.mk_Tm_app head args)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r
                               in
                            let uu____7019 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____7012, comp, uu____7019))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7034 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____7034 with
                      | (bs,c) ->
                          let head_info =
                            (head, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c))
                             in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs args)
                 | uu____7077 ->
                     (match Prims.op_Negation norm with
                      | true  ->
                          let uu____7083 = unfold_whnf env tf  in
                          check_function_app true uu____7083
                      | uu____7084 ->
                          let uu____7085 =
                            let uu____7086 =
                              let uu____7089 =
                                FStar_TypeChecker_Err.expected_function_typ
                                  env tf
                                 in
                              (uu____7089, (head.FStar_Syntax_Syntax.pos))
                               in
                            FStar_Errors.Error uu____7086  in
                          Prims.raise uu____7085)
                  in
               let uu____7095 =
                 let uu____7096 = FStar_Syntax_Util.unrefine thead  in
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.WHNF] env uu____7096
                  in
               check_function_app false uu____7095)

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
    fun head  ->
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
                  let uu____7142 =
                    FStar_List.fold_left2
                      (fun uu____7155  ->
                         fun uu____7156  ->
                           fun uu____7157  ->
                             match (uu____7155, uu____7156, uu____7157) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((match aq <> aq' with
                                   | true  ->
                                       Prims.raise
                                         (FStar_Errors.Error
                                            ("Inconsistent implicit qualifiers",
                                              (e.FStar_Syntax_Syntax.pos)))
                                   | uu____7200 -> ());
                                  (let uu____7201 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____7201 with
                                   | (e,c,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen
                                          in
                                       let g =
                                         let uu____7213 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7213 g
                                          in
                                       let ghost =
                                         ghost ||
                                           ((let uu____7215 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c
                                                in
                                             Prims.op_Negation uu____7215) &&
                                              (let uu____7216 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____7216))
                                          in
                                       let uu____7217 =
                                         let uu____7223 =
                                           let uu____7229 =
                                             FStar_Syntax_Syntax.as_arg e  in
                                           [uu____7229]  in
                                         FStar_List.append seen uu____7223
                                          in
                                       let uu____7234 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g
                                          in
                                       (uu____7217, uu____7234, ghost))))
                      ([], g_head, false) args bs
                     in
                  (match uu____7142 with
                   | (args,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head args)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r
                          in
                       let c =
                         match ghost with
                         | true  ->
                             let uu____7263 =
                               FStar_Syntax_Syntax.mk_GTotal res_t  in
                             FStar_All.pipe_right uu____7263
                               FStar_Syntax_Util.lcomp_of_comp
                         | uu____7264 -> FStar_Syntax_Util.lcomp_of_comp c
                          in
                       let uu____7265 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c guard
                          in
                       (match uu____7265 with | (c,g) -> (e, c, g)))
              | uu____7277 ->
                  check_application_args env head chead g_head args
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
      fun branch  ->
        let uu____7299 = FStar_Syntax_Subst.open_branch branch  in
        match uu____7299 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7325 = branch  in
            (match uu____7325 with
             | (cpat,uu____7345,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7387 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0
                      in
                   match uu____7387 with
                   | (pat_bvs,exps,p) ->
                       ((let uu____7409 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         match uu____7409 with
                         | true  ->
                             let uu____7410 =
                               FStar_Syntax_Print.pat_to_string p0  in
                             let uu____7411 =
                               FStar_Syntax_Print.pat_to_string p  in
                             FStar_Util.print2
                               "Pattern %s elaborated to %s\n" uu____7410
                               uu____7411
                         | uu____7412 -> ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs
                            in
                         let uu____7414 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____7414 with
                         | (env1,uu____7427) ->
                             let env1 =
                               let uu___110_7431 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___110_7431.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___110_7431.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___110_7431.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___110_7431.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___110_7431.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___110_7431.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___110_7431.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___110_7431.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___110_7431.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___110_7431.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___110_7431.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___110_7431.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___110_7431.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___110_7431.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___110_7431.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___110_7431.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___110_7431.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___110_7431.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___110_7431.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___110_7431.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___110_7431.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___110_7431.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___110_7431.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             let uu____7433 =
                               let uu____7438 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____7450 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High
                                             in
                                          match uu____7450 with
                                          | true  ->
                                              let uu____7451 =
                                                FStar_Syntax_Print.term_to_string
                                                  e
                                                 in
                                              let uu____7452 =
                                                FStar_Syntax_Print.term_to_string
                                                  pat_t
                                                 in
                                              FStar_Util.print2
                                                "Checking pattern expression %s against expected type %s\n"
                                                uu____7451 uu____7452
                                          | uu____7453 -> ());
                                         (let uu____7454 = tc_term env1 e  in
                                          match uu____7454 with
                                          | (e,lc,g) ->
                                              ((let uu____7464 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High
                                                   in
                                                match uu____7464 with
                                                | true  ->
                                                    let uu____7465 =
                                                      FStar_TypeChecker_Normalize.term_to_string
                                                        env e
                                                       in
                                                    let uu____7466 =
                                                      FStar_TypeChecker_Normalize.term_to_string
                                                        env
                                                        lc.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_Util.print2
                                                      "Pre-checked pattern expression %s at type %s\n"
                                                      uu____7465 uu____7466
                                                | uu____7467 -> ());
                                               (let g' =
                                                  FStar_TypeChecker_Rel.teq
                                                    env
                                                    lc.FStar_Syntax_Syntax.res_typ
                                                    expected_pat_t
                                                   in
                                                let g =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g'
                                                   in
                                                let uu____7470 =
                                                  let uu____7471 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___111_7472 = g
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___111_7472.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___111_7472.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___111_7472.FStar_TypeChecker_Env.implicits)
                                                       })
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____7471
                                                    FStar_TypeChecker_Rel.resolve_implicits
                                                   in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e
                                                   in
                                                let uvars_to_string uvs =
                                                  let uu____7486 =
                                                    let uu____7488 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____7488
                                                      (FStar_List.map
                                                         (fun uu____7512  ->
                                                            match uu____7512
                                                            with
                                                            | (u,uu____7517)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u))
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____7486
                                                    (FStar_String.concat ", ")
                                                   in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e'
                                                   in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t
                                                   in
                                                (let uu____7530 =
                                                   let uu____7531 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2
                                                      in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation
                                                     uu____7531
                                                    in
                                                 match uu____7530 with
                                                 | true  ->
                                                     let unresolved =
                                                       let uu____7538 =
                                                         FStar_Util.set_difference
                                                           uvs1 uvs2
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____7538
                                                         FStar_Util.set_elements
                                                        in
                                                     let uu____7552 =
                                                       let uu____7553 =
                                                         let uu____7556 =
                                                           let uu____7557 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e'
                                                              in
                                                           let uu____7558 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env
                                                               expected_pat_t
                                                              in
                                                           let uu____7559 =
                                                             let uu____7560 =
                                                               FStar_All.pipe_right
                                                                 unresolved
                                                                 (FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____7572
                                                                     ->
                                                                    match uu____7572
                                                                    with
                                                                    | 
                                                                    (u,uu____7580)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u))
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____7560
                                                               (FStar_String.concat
                                                                  ", ")
                                                              in
                                                           FStar_Util.format3
                                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                             uu____7557
                                                             uu____7558
                                                             uu____7559
                                                            in
                                                         (uu____7556,
                                                           (p.FStar_Syntax_Syntax.p))
                                                          in
                                                       FStar_Errors.Error
                                                         uu____7553
                                                        in
                                                     Prims.raise uu____7552
                                                 | uu____7593 -> ());
                                                (let uu____7595 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High
                                                    in
                                                 match uu____7595 with
                                                 | true  ->
                                                     let uu____7596 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e
                                                        in
                                                     FStar_Util.print1
                                                       "Done checking pattern expression %s\n"
                                                       uu____7596
                                                 | uu____7597 -> ());
                                                (e, e'))))))
                                  in
                               FStar_All.pipe_right uu____7438
                                 FStar_List.unzip
                                in
                             (match uu____7433 with
                              | (exps,norm_exps) ->
                                  let p =
                                    FStar_TypeChecker_Util.decorate_pattern
                                      env p exps
                                     in
                                  (p, pat_bvs, pat_env, exps, norm_exps))))
                    in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____7627 =
                   let uu____7631 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____7631
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____7627 with
                  | (scrutinee_env,uu____7644) ->
                      let uu____7647 = tc_pat true pat_t pattern  in
                      (match uu____7647 with
                       | (pattern,pat_bvs,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____7675 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____7690 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 (match uu____7690 with
                                  | true  ->
                                      Prims.raise
                                        (FStar_Errors.Error
                                           ("When clauses are not yet supported in --verify mode; they will be some day",
                                             (e.FStar_Syntax_Syntax.pos)))
                                  | uu____7697 ->
                                      let uu____7698 =
                                        let uu____7702 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env
                                            FStar_TypeChecker_Common.t_bool
                                           in
                                        tc_term uu____7702 e  in
                                      (match uu____7698 with
                                       | (e,c,g) -> ((Some e), g)))
                              in
                           (match uu____7675 with
                            | (when_clause,g_when) ->
                                let uu____7722 = tc_term pat_env branch_exp
                                   in
                                (match uu____7722 with
                                 | (branch_exp,c,g_branch) ->
                                     let when_condition =
                                       match when_clause with
                                       | None  -> None
                                       | Some w ->
                                           let uu____7747 =
                                             FStar_Syntax_Util.mk_eq
                                               FStar_Syntax_Util.t_bool
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_30  -> Some _0_30)
                                             uu____7747
                                        in
                                     let uu____7757 =
                                       let eqs =
                                         let uu____7765 =
                                           let uu____7766 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____7766  in
                                         match uu____7765 with
                                         | true  -> None
                                         | uu____7772 ->
                                             FStar_All.pipe_right disj_exps
                                               (FStar_List.fold_left
                                                  (fun fopt  ->
                                                     fun e  ->
                                                       let e =
                                                         FStar_Syntax_Subst.compress
                                                           e
                                                          in
                                                       match e.FStar_Syntax_Syntax.n
                                                       with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                         _
                                                         |FStar_Syntax_Syntax.Tm_constant
                                                          _
                                                          |FStar_Syntax_Syntax.Tm_fvar
                                                          _ -> fopt
                                                       | uu____7792 ->
                                                           let clause =
                                                             FStar_Syntax_Util.mk_eq
                                                               pat_t pat_t
                                                               scrutinee_tm e
                                                              in
                                                           (match fopt with
                                                            | None  ->
                                                                Some clause
                                                            | Some f ->
                                                                let uu____7812
                                                                  =
                                                                  FStar_Syntax_Util.mk_disj
                                                                    clause f
                                                                   in
                                                                FStar_All.pipe_left
                                                                  (fun _0_31 
                                                                    ->
                                                                    Some
                                                                    _0_31)
                                                                  uu____7812))
                                                  None)
                                          in
                                       let uu____7824 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp c g_branch
                                          in
                                       match uu____7824 with
                                       | (c,g_branch) ->
                                           let uu____7834 =
                                             match (eqs, when_condition) with
                                             | uu____7845 when
                                                 let uu____7854 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation uu____7854
                                                 -> (c, g_when)
                                             | (None ,None ) -> (c, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf
                                                    in
                                                 let uu____7880 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c gf
                                                    in
                                                 let uu____7881 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____7880, uu____7881)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____7900 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____7900
                                                    in
                                                 let uu____7901 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c g_fw
                                                    in
                                                 let uu____7902 =
                                                   let uu____7903 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____7903 g_when
                                                    in
                                                 (uu____7901, uu____7902)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let uu____7919 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c g_w
                                                    in
                                                 (uu____7919, g_when)
                                              in
                                           (match uu____7834 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs
                                                   in
                                                let uu____7927 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs c_weak
                                                   in
                                                let uu____7928 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    binders g_when_weak
                                                   in
                                                (uu____7927, uu____7928,
                                                  g_branch))
                                        in
                                     (match uu____7757 with
                                      | (c,g_when,g_branch) ->
                                          let branch_guard =
                                            let uu____7941 =
                                              let uu____7942 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____7942
                                               in
                                            match uu____7941 with
                                            | true  ->
                                                FStar_Syntax_Util.t_true
                                            | uu____7943 ->
                                                let rec build_branch_guard
                                                  scrutinee_tm pat_exp =
                                                  let discriminate
                                                    scrutinee_tm f =
                                                    let uu____7975 =
                                                      let uu____7976 =
                                                        let uu____7977 =
                                                          let uu____7979 =
                                                            let uu____7983 =
                                                              FStar_TypeChecker_Env.typ_of_datacon
                                                                env
                                                                f.FStar_Syntax_Syntax.v
                                                               in
                                                            FStar_TypeChecker_Env.datacons_of_typ
                                                              env uu____7983
                                                             in
                                                          Prims.snd
                                                            uu____7979
                                                           in
                                                        FStar_List.length
                                                          uu____7977
                                                         in
                                                      uu____7976 >
                                                        (Prims.parse_int "1")
                                                       in
                                                    match uu____7975 with
                                                    | true  ->
                                                        let discriminator =
                                                          FStar_Syntax_Util.mk_discriminator
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        let uu____7994 =
                                                          FStar_TypeChecker_Env.try_lookup_lid
                                                            env discriminator
                                                           in
                                                        (match uu____7994
                                                         with
                                                         | None  -> []
                                                         | uu____8005 ->
                                                             let disc =
                                                               FStar_Syntax_Syntax.fvar
                                                                 discriminator
                                                                 FStar_Syntax_Syntax.Delta_equational
                                                                 None
                                                                in
                                                             let disc =
                                                               let uu____8013
                                                                 =
                                                                 let uu____8014
                                                                   =
                                                                   let uu____8015
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm
                                                                     in
                                                                   [uu____8015]
                                                                    in
                                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                                   disc
                                                                   uu____8014
                                                                  in
                                                               uu____8013
                                                                 None
                                                                 scrutinee_tm.FStar_Syntax_Syntax.pos
                                                                in
                                                             let uu____8020 =
                                                               FStar_Syntax_Util.mk_eq
                                                                 FStar_Syntax_Util.t_bool
                                                                 FStar_Syntax_Util.t_bool
                                                                 disc
                                                                 FStar_Syntax_Const.exp_true_bool
                                                                in
                                                             [uu____8020])
                                                    | uu____8027 -> []  in
                                                  let fail uu____8036 =
                                                    let uu____8037 =
                                                      let uu____8038 =
                                                        FStar_Range.string_of_range
                                                          pat_exp.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____8039 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp
                                                         in
                                                      let uu____8040 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____8038 uu____8039
                                                        uu____8040
                                                       in
                                                    failwith uu____8037  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t,uu____8061) ->
                                                        head_constructor t
                                                    | uu____8067 -> fail ()
                                                     in
                                                  let pat_exp =
                                                    let uu____8070 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____8070
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match pat_exp.FStar_Syntax_Syntax.n
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
                                                      uu____8086 ->
                                                      let uu____8087 =
                                                        let uu____8090 =
                                                          let uu____8091 =
                                                            let uu____8092 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                scrutinee_tm
                                                               in
                                                            let uu____8093 =
                                                              let uu____8095
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  pat_exp
                                                                 in
                                                              [uu____8095]
                                                               in
                                                            uu____8092 ::
                                                              uu____8093
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            FStar_Syntax_Util.teq
                                                            uu____8091
                                                           in
                                                        uu____8090 None
                                                          scrutinee_tm.FStar_Syntax_Syntax.pos
                                                         in
                                                      [uu____8087]
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                    _
                                                    |FStar_Syntax_Syntax.Tm_fvar
                                                    _ ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp
                                                         in
                                                      let uu____8111 =
                                                        let uu____8112 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____8112
                                                         in
                                                      (match uu____8111 with
                                                       | true  -> []
                                                       | uu____8118 ->
                                                           let uu____8119 =
                                                             head_constructor
                                                               pat_exp
                                                              in
                                                           discriminate
                                                             scrutinee_tm
                                                             uu____8119)
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head,args) ->
                                                      let f =
                                                        head_constructor head
                                                         in
                                                      let uu____8146 =
                                                        let uu____8147 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____8147
                                                         in
                                                      (match uu____8146 with
                                                       | true  -> []
                                                       | uu____8153 ->
                                                           let sub_term_guards
                                                             =
                                                             let uu____8156 =
                                                               FStar_All.pipe_right
                                                                 args
                                                                 (FStar_List.mapi
                                                                    (
                                                                    fun i  ->
                                                                    fun
                                                                    uu____8172
                                                                     ->
                                                                    match uu____8172
                                                                    with
                                                                    | 
                                                                    (ei,uu____8179)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____8189
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____8189
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8196
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8203
                                                                    =
                                                                    let uu____8204
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None  in
                                                                    let uu____8209
                                                                    =
                                                                    let uu____8210
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm
                                                                     in
                                                                    [uu____8210]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8204
                                                                    uu____8209
                                                                     in
                                                                    uu____8203
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____8156
                                                               FStar_List.flatten
                                                              in
                                                           let uu____8222 =
                                                             discriminate
                                                               scrutinee_tm f
                                                              in
                                                           FStar_List.append
                                                             uu____8222
                                                             sub_term_guards)
                                                  | uu____8230 -> []  in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm pat =
                                                  let uu____8242 =
                                                    let uu____8243 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____8243
                                                     in
                                                  match uu____8242 with
                                                  | true  ->
                                                      FStar_TypeChecker_Util.fvar_const
                                                        env
                                                        FStar_Syntax_Const.true_lid
                                                  | uu____8244 ->
                                                      let t =
                                                        let uu____8246 =
                                                          build_branch_guard
                                                            scrutinee_tm pat
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.mk_conj_l
                                                          uu____8246
                                                         in
                                                      let uu____8249 =
                                                        FStar_Syntax_Util.type_u
                                                          ()
                                                         in
                                                      (match uu____8249 with
                                                       | (k,uu____8253) ->
                                                           let uu____8254 =
                                                             tc_check_tot_or_gtot_term
                                                               scrutinee_env
                                                               t k
                                                              in
                                                           (match uu____8254
                                                            with
                                                            | (t,uu____8259,uu____8260)
                                                                -> t))
                                                   in
                                                let branch_guard =
                                                  let uu____8262 =
                                                    FStar_All.pipe_right
                                                      norm_disj_exps
                                                      (FStar_List.map
                                                         (build_and_check_branch_guard
                                                            scrutinee_tm))
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____8262
                                                    FStar_Syntax_Util.mk_disj_l
                                                   in
                                                let branch_guard =
                                                  match when_condition with
                                                  | None  -> branch_guard
                                                  | Some w ->
                                                      FStar_Syntax_Util.mk_conj
                                                        branch_guard w
                                                   in
                                                branch_guard
                                             in
                                          let guard =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when g_branch
                                             in
                                          ((let uu____8279 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            match uu____8279 with
                                            | true  ->
                                                let uu____8280 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____8280
                                            | uu____8281 -> ());
                                           (let uu____8282 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern, when_clause,
                                                  branch_exp)
                                               in
                                            (uu____8282, branch_guard, c,
                                              guard)))))))))

and check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____8300 = check_let_bound_def true env lb  in
          (match uu____8300 with
           | (e1,univ_vars,c1,g1,annotated) ->
               let uu____8314 =
                 match annotated &&
                         (Prims.op_Negation
                            env.FStar_TypeChecker_Env.generalize)
                 with
                 | true  -> (g1, e1, univ_vars, c1)
                 | uu____8323 ->
                     let g1 =
                       let uu____8325 =
                         FStar_TypeChecker_Rel.solve_deferred_constraints env
                           g1
                          in
                       FStar_All.pipe_right uu____8325
                         FStar_TypeChecker_Rel.resolve_implicits
                        in
                     let uu____8327 =
                       let uu____8332 =
                         let uu____8338 =
                           let uu____8343 =
                             let uu____8351 = c1.FStar_Syntax_Syntax.comp ()
                                in
                             ((lb.FStar_Syntax_Syntax.lbname), e1,
                               uu____8351)
                              in
                           [uu____8343]  in
                         FStar_TypeChecker_Util.generalize env uu____8338  in
                       FStar_List.hd uu____8332  in
                     (match uu____8327 with
                      | (uu____8380,univs,e1,c1) ->
                          (g1, e1, univs,
                            (FStar_Syntax_Util.lcomp_of_comp c1)))
                  in
               (match uu____8314 with
                | (g1,e1,univ_vars,c1) ->
                    let uu____8391 =
                      let uu____8396 =
                        FStar_TypeChecker_Env.should_verify env  in
                      match uu____8396 with
                      | true  ->
                          let uu____8401 =
                            FStar_TypeChecker_Util.check_top_level env g1 c1
                             in
                          (match uu____8401 with
                           | (ok,c1) ->
                               (match ok with
                                | true  -> (e2, c1)
                                | uu____8416 ->
                                    ((let uu____8418 =
                                        FStar_Options.warn_top_level_effects
                                          ()
                                         in
                                      match uu____8418 with
                                      | true  ->
                                          let uu____8419 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          FStar_Errors.warn uu____8419
                                            FStar_TypeChecker_Err.top_level_effect
                                      | uu____8420 -> ());
                                     (let uu____8421 =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_meta
                                              (e2,
                                                (FStar_Syntax_Syntax.Meta_desugared
                                                   FStar_Syntax_Syntax.Masked_effect))))
                                          None e2.FStar_Syntax_Syntax.pos
                                         in
                                      (uu____8421, c1)))))
                      | uu____8436 ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                           (let c =
                              let uu____8439 = c1.FStar_Syntax_Syntax.comp ()
                                 in
                              FStar_All.pipe_right uu____8439
                                (FStar_TypeChecker_Normalize.normalize_comp
                                   [FStar_TypeChecker_Normalize.Beta] env)
                               in
                            let e2 =
                              let uu____8447 =
                                FStar_Syntax_Util.is_pure_comp c  in
                              match uu____8447 with
                              | true  -> e2
                              | uu____8450 ->
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect))))
                                    None e2.FStar_Syntax_Syntax.pos
                               in
                            (e2, c)))
                       in
                    (match uu____8391 with
                     | (e2,c1) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env
                             (FStar_Syntax_Util.comp_effect_name c1)
                             FStar_Syntax_Syntax.U_zero
                             FStar_TypeChecker_Common.t_unit
                            in
                         (FStar_ST.write e2.FStar_Syntax_Syntax.tk
                            (Some
                               (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                          (let lb =
                             FStar_Syntax_Util.close_univs_and_mk_letbinding
                               None lb.FStar_Syntax_Syntax.lbname univ_vars
                               (FStar_Syntax_Util.comp_result c1)
                               (FStar_Syntax_Util.comp_effect_name c1) e1
                              in
                           let uu____8479 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb]), e2)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos
                              in
                           (uu____8479,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8498 -> failwith "Impossible"

and check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env =
            let uu___112_8519 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___112_8519.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___112_8519.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___112_8519.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___112_8519.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___112_8519.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___112_8519.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___112_8519.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___112_8519.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___112_8519.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___112_8519.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___112_8519.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___112_8519.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___112_8519.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___112_8519.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___112_8519.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___112_8519.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___112_8519.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___112_8519.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___112_8519.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___112_8519.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___112_8519.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___112_8519.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___112_8519.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____8520 =
            let uu____8526 =
              let uu____8527 = FStar_TypeChecker_Env.clear_expected_typ env
                 in
              FStar_All.pipe_right uu____8527 Prims.fst  in
            check_let_bound_def false uu____8526 lb  in
          (match uu____8520 with
           | (e1,uu____8539,c1,g1,annotated) ->
               let x =
                 let uu___113_8544 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___113_8544.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___113_8544.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 }  in
               let uu____8545 =
                 let uu____8548 =
                   let uu____8549 = FStar_Syntax_Syntax.mk_binder x  in
                   [uu____8549]  in
                 FStar_Syntax_Subst.open_term uu____8548 e2  in
               (match uu____8545 with
                | (xb,e2) ->
                    let xbinder = FStar_List.hd xb  in
                    let x = Prims.fst xbinder  in
                    let uu____8561 =
                      let uu____8565 = FStar_TypeChecker_Env.push_bv env x
                         in
                      tc_term uu____8565 e2  in
                    (match uu____8561 with
                     | (e2,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.bind
                             e1.FStar_Syntax_Syntax.pos env (Some e1) c1
                             ((Some x), c2)
                            in
                         let e1 =
                           FStar_TypeChecker_Util.maybe_lift env e1
                             c1.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.eff_name
                             c1.FStar_Syntax_Syntax.res_typ
                            in
                         let e2 =
                           FStar_TypeChecker_Util.maybe_lift env e2
                             c2.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.eff_name
                             c2.FStar_Syntax_Syntax.res_typ
                            in
                         let lb =
                           FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl x)
                             [] c1.FStar_Syntax_Syntax.res_typ
                             c1.FStar_Syntax_Syntax.eff_name e1
                            in
                         let e =
                           let uu____8580 =
                             let uu____8583 =
                               let uu____8584 =
                                 let uu____8592 =
                                   FStar_Syntax_Subst.close xb e2  in
                                 ((false, [lb]), uu____8592)  in
                               FStar_Syntax_Syntax.Tm_let uu____8584  in
                             FStar_Syntax_Syntax.mk uu____8583  in
                           uu____8580
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos
                            in
                         let e =
                           FStar_TypeChecker_Util.maybe_monadic env e
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ
                            in
                         let x_eq_e1 =
                           let uu____8607 =
                             let uu____8608 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             FStar_Syntax_Util.mk_eq
                               c1.FStar_Syntax_Syntax.res_typ
                               c1.FStar_Syntax_Syntax.res_typ uu____8608 e1
                              in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8607
                            in
                         let g2 =
                           let uu____8614 =
                             let uu____8615 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard uu____8615 g2
                              in
                           FStar_TypeChecker_Rel.close_guard xb uu____8614
                            in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g2
                            in
                         let uu____8617 =
                           let uu____8618 =
                             FStar_TypeChecker_Env.expected_typ env  in
                           FStar_Option.isSome uu____8618  in
                         (match uu____8617 with
                          | true  ->
                              let tt =
                                let uu____8624 =
                                  FStar_TypeChecker_Env.expected_typ env  in
                                FStar_All.pipe_right uu____8624
                                  FStar_Option.get
                                 in
                              ((let uu____8628 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Exports")
                                   in
                                match uu____8628 with
                                | true  ->
                                    let uu____8629 =
                                      FStar_Syntax_Print.term_to_string tt
                                       in
                                    let uu____8630 =
                                      FStar_Syntax_Print.term_to_string
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    FStar_Util.print2
                                      "Got expected type from env %s\ncres.res_typ=%s\n"
                                      uu____8629 uu____8630
                                | uu____8631 -> ());
                               (e, cres, guard))
                          | uu____8632 ->
                              let t =
                                check_no_escape None env [x]
                                  cres.FStar_Syntax_Syntax.res_typ
                                 in
                              ((let uu____8635 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Exports")
                                   in
                                match uu____8635 with
                                | true  ->
                                    let uu____8636 =
                                      FStar_Syntax_Print.term_to_string
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    let uu____8637 =
                                      FStar_Syntax_Print.term_to_string t  in
                                    FStar_Util.print2
                                      "Checked %s has no escaping types; normalized to %s\n"
                                      uu____8636 uu____8637
                                | uu____8638 -> ());
                               (e,
                                 ((let uu___114_8639 = cres  in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___114_8639.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ = t;
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___114_8639.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (uu___114_8639.FStar_Syntax_Syntax.comp)
                                   })), guard))))))
      | uu____8640 -> failwith "Impossible"

and check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun top  ->
      let env = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____8661 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____8661 with
           | (lbs,e2) ->
               let uu____8672 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____8672 with
                | (env0,topt) ->
                    let uu____8683 = build_let_rec_env true env0 lbs  in
                    (match uu____8683 with
                     | (lbs,rec_env) ->
                         let uu____8694 = check_let_recs rec_env lbs  in
                         (match uu____8694 with
                          | (lbs,g_lbs) ->
                              let g_lbs =
                                let uu____8706 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env g_lbs
                                   in
                                FStar_All.pipe_right uu____8706
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____8710 =
                                  FStar_All.pipe_right lbs
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____8710
                                  (fun _0_33  -> Some _0_33)
                                 in
                              let lbs =
                                match Prims.op_Negation
                                        env.FStar_TypeChecker_Env.generalize
                                with
                                | true  ->
                                    FStar_All.pipe_right lbs
                                      (FStar_List.map
                                         (fun lb  ->
                                            match lb.FStar_Syntax_Syntax.lbunivs
                                                    = []
                                            with
                                            | true  -> lb
                                            | uu____8726 ->
                                                FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                  all_lb_names
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  lb.FStar_Syntax_Syntax.lbunivs
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                  lb.FStar_Syntax_Syntax.lbeff
                                                  lb.FStar_Syntax_Syntax.lbdef))
                                | uu____8727 ->
                                    let ecs =
                                      let uu____8734 =
                                        FStar_All.pipe_right lbs
                                          (FStar_List.map
                                             (fun lb  ->
                                                let uu____8756 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    lb.FStar_Syntax_Syntax.lbtyp
                                                   in
                                                ((lb.FStar_Syntax_Syntax.lbname),
                                                  (lb.FStar_Syntax_Syntax.lbdef),
                                                  uu____8756)))
                                         in
                                      FStar_TypeChecker_Util.generalize env
                                        uu____8734
                                       in
                                    FStar_All.pipe_right ecs
                                      (FStar_List.map
                                         (fun uu____8776  ->
                                            match uu____8776 with
                                            | (x,uvs,e,c) ->
                                                FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                  all_lb_names x uvs
                                                  (FStar_Syntax_Util.comp_result
                                                     c)
                                                  (FStar_Syntax_Util.comp_effect_name
                                                     c) e))
                                 in
                              let cres =
                                let uu____8801 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____8801
                                 in
                              (FStar_ST.write e2.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____8810 =
                                  FStar_Syntax_Subst.close_let_rec lbs e2  in
                                match uu____8810 with
                                | (lbs,e2) ->
                                    let uu____8821 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs), e2)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____8836 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env g_lbs
                                       in
                                    (uu____8821, cres, uu____8836)))))))
      | uu____8839 -> failwith "Impossible"

and check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun top  ->
      let env = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____8860 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____8860 with
           | (lbs,e2) ->
               let uu____8871 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____8871 with
                | (env0,topt) ->
                    let uu____8882 = build_let_rec_env false env0 lbs  in
                    (match uu____8882 with
                     | (lbs,rec_env) ->
                         let uu____8893 = check_let_recs rec_env lbs  in
                         (match uu____8893 with
                          | (lbs,g_lbs) ->
                              let uu____8904 =
                                FStar_All.pipe_right lbs
                                  (FStar_Util.fold_map
                                     (fun env  ->
                                        fun lb  ->
                                          let x =
                                            let uu___115_8915 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___115_8915.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___115_8915.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb =
                                            let uu___116_8917 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___116_8917.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___116_8917.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___116_8917.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___116_8917.FStar_Syntax_Syntax.lbdef)
                                            }  in
                                          let env =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env
                                              lb.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb.FStar_Syntax_Syntax.lbtyp))
                                             in
                                          (env, lb)) env)
                                 in
                              (match uu____8904 with
                               | (env,lbs) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____8934 = tc_term env e2  in
                                   (match uu____8934 with
                                    | (e2,cres,g2) ->
                                        let guard =
                                          let uu____8945 =
                                            let uu____8946 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              uu____8946 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____8945
                                           in
                                        let cres =
                                          FStar_TypeChecker_Util.close_comp
                                            env bvs cres
                                           in
                                        let tres =
                                          norm env
                                            cres.FStar_Syntax_Syntax.res_typ
                                           in
                                        let cres =
                                          let uu___117_8950 = cres  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___117_8950.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___117_8950.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___117_8950.FStar_Syntax_Syntax.comp)
                                          }  in
                                        let uu____8951 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs e2
                                           in
                                        (match uu____8951 with
                                         | (lbs,e2) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs), e2)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos
                                                in
                                             (match topt with
                                              | Some uu____8980 ->
                                                  (e, cres, guard)
                                              | None  ->
                                                  let tres =
                                                    check_no_escape None env
                                                      bvs tres
                                                     in
                                                  let cres =
                                                    let uu___118_8985 = cres
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___118_8985.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___118_8985.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___118_8985.FStar_Syntax_Syntax.comp)
                                                    }  in
                                                  (e, cres, guard)))))))))
      | uu____8988 -> failwith "Impossible"

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
          let uu____9004 = FStar_Syntax_Util.arrow_formals_comp t  in
          match uu____9004 with
          | (uu____9010,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c)
                 in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)
           in
        let uu____9021 =
          FStar_List.fold_left
            (fun uu____9028  ->
               fun lb  ->
                 match uu____9028 with
                 | (lbs,env) ->
                     let uu____9040 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env
                         lb
                        in
                     (match uu____9040 with
                      | (univ_vars,t,check_t) ->
                          let env =
                            FStar_TypeChecker_Env.push_univ_vars env
                              univ_vars
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let t =
                            match Prims.op_Negation check_t with
                            | true  -> t
                            | uu____9053 ->
                                let uu____9054 =
                                  let uu____9058 =
                                    let uu____9059 =
                                      FStar_Syntax_Util.type_u ()  in
                                    FStar_All.pipe_left Prims.fst uu____9059
                                     in
                                  tc_check_tot_or_gtot_term
                                    (let uu___119_9064 = env0  in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___119_9064.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___119_9064.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___119_9064.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___119_9064.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___119_9064.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___119_9064.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___119_9064.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___119_9064.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___119_9064.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___119_9064.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___119_9064.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___119_9064.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___119_9064.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___119_9064.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         true;
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___119_9064.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___119_9064.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___119_9064.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___119_9064.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___119_9064.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___119_9064.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___119_9064.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         (uu___119_9064.FStar_TypeChecker_Env.use_bv_sorts);
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___119_9064.FStar_TypeChecker_Env.qname_and_index)
                                     }) t uu____9058
                                   in
                                (match uu____9054 with
                                 | (t,uu____9066,g) ->
                                     let g =
                                       FStar_TypeChecker_Rel.resolve_implicits
                                         g
                                        in
                                     ((let uu____9070 =
                                         FStar_TypeChecker_Rel.discharge_guard
                                           env g
                                          in
                                       FStar_All.pipe_left Prims.ignore
                                         uu____9070);
                                      norm env0 t))
                             in
                          let env =
                            let uu____9072 =
                              (termination_check_enabled t) &&
                                (FStar_TypeChecker_Env.should_verify env)
                               in
                            match uu____9072 with
                            | true  ->
                                let uu___120_9073 = env  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___120_9073.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___120_9073.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___120_9073.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___120_9073.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___120_9073.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___120_9073.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___120_9073.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___120_9073.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___120_9073.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___120_9073.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___120_9073.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___120_9073.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (((lb.FStar_Syntax_Syntax.lbname), t) ::
                                    (env.FStar_TypeChecker_Env.letrecs));
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___120_9073.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___120_9073.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___120_9073.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___120_9073.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___120_9073.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___120_9073.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___120_9073.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___120_9073.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___120_9073.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___120_9073.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___120_9073.FStar_TypeChecker_Env.qname_and_index)
                                }
                            | uu____9080 ->
                                FStar_TypeChecker_Env.push_let_binding env
                                  lb.FStar_Syntax_Syntax.lbname ([], t)
                             in
                          let lb =
                            let uu___121_9083 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___121_9083.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars;
                              FStar_Syntax_Syntax.lbtyp = t;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___121_9083.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb :: lbs), env))) ([], env) lbs
           in
        match uu____9021 with | (lbs,env) -> ((FStar_List.rev lbs), env)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9097 =
        let uu____9102 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____9113 =
                    let uu____9117 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    tc_tot_or_gtot_term uu____9117
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____9113 with
                  | (e,c,g) ->
                      ((let uu____9124 =
                          let uu____9125 = FStar_Syntax_Util.is_total_lcomp c
                             in
                          Prims.op_Negation uu____9125  in
                        match uu____9124 with
                        | true  ->
                            Prims.raise
                              (FStar_Errors.Error
                                 ("Expected let rec to be a Tot term; got effect GTot",
                                   (e.FStar_Syntax_Syntax.pos)))
                        | uu____9126 -> ());
                       (let lb =
                          FStar_Syntax_Util.mk_letbinding
                            lb.FStar_Syntax_Syntax.lbname
                            lb.FStar_Syntax_Syntax.lbunivs
                            lb.FStar_Syntax_Syntax.lbtyp
                            FStar_Syntax_Const.effect_Tot_lid e
                           in
                        (lb, g)))))
           in
        FStar_All.pipe_right uu____9102 FStar_List.unzip  in
      match uu____9097 with
      | (lbs,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs
              FStar_TypeChecker_Rel.trivial_guard
             in
          (lbs, g_lbs)

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
        let uu____9154 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____9154 with
        | (env1,uu____9164) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____9170 = check_lbtyp top_level env lb  in
            (match uu____9170 with
             | (topt,wf_annot,univ_vars,univ_opening,env1) ->
                 ((match (Prims.op_Negation top_level) && (univ_vars <> [])
                   with
                   | true  ->
                       Prims.raise
                         (FStar_Errors.Error
                            ("Inner let-bound definitions cannot be universe polymorphic",
                              (e1.FStar_Syntax_Syntax.pos)))
                   | uu____9193 -> ());
                  (let e1 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____9196 =
                     tc_maybe_toplevel_term
                       (let uu___122_9200 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___122_9200.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___122_9200.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___122_9200.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___122_9200.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___122_9200.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___122_9200.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___122_9200.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___122_9200.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___122_9200.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___122_9200.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___122_9200.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___122_9200.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___122_9200.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___122_9200.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___122_9200.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___122_9200.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___122_9200.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___122_9200.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___122_9200.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___122_9200.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___122_9200.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___122_9200.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___122_9200.FStar_TypeChecker_Env.qname_and_index)
                        }) e1
                      in
                   match uu____9196 with
                   | (e1,c1,g1) ->
                       let uu____9209 =
                         let uu____9212 =
                           FStar_TypeChecker_Env.set_range env1
                             e1.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9215  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9212 e1 c1 wf_annot
                          in
                       (match uu____9209 with
                        | (c1,guard_f) ->
                            let g1 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____9225 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              match uu____9225 with
                              | true  ->
                                  let uu____9226 =
                                    FStar_Syntax_Print.lbname_to_string
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  let uu____9227 =
                                    FStar_Syntax_Print.term_to_string
                                      c1.FStar_Syntax_Syntax.res_typ
                                     in
                                  let uu____9228 =
                                    FStar_TypeChecker_Rel.guard_to_string env
                                      g1
                                     in
                                  FStar_Util.print3
                                    "checked top-level def %s, result type is %s, guard is %s\n"
                                    uu____9226 uu____9227 uu____9228
                              | uu____9229 -> ());
                             (e1, univ_vars, c1, g1,
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
            ((match lb.FStar_Syntax_Syntax.lbunivs <> [] with
              | true  ->
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
              | uu____9250 -> ());
             (None, FStar_TypeChecker_Rel.trivial_guard, [], [], env))
        | uu____9254 ->
            let uu____9255 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____9255 with
             | (univ_opening,univ_vars) ->
                 let t = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 (match top_level &&
                          (Prims.op_Negation
                             env.FStar_TypeChecker_Env.generalize)
                  with
                  | true  ->
                      let uu____9282 =
                        FStar_TypeChecker_Env.set_expected_typ env1 t  in
                      ((Some t), FStar_TypeChecker_Rel.trivial_guard,
                        univ_vars, univ_opening, uu____9282)
                  | uu____9286 ->
                      let uu____9287 = FStar_Syntax_Util.type_u ()  in
                      (match uu____9287 with
                       | (k,uu____9298) ->
                           let uu____9299 =
                             tc_check_tot_or_gtot_term env1 t k  in
                           (match uu____9299 with
                            | (t,uu____9311,g) ->
                                ((let uu____9314 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Medium
                                     in
                                  match uu____9314 with
                                  | true  ->
                                      let uu____9315 =
                                        let uu____9316 =
                                          FStar_Syntax_Syntax.range_of_lbname
                                            lb.FStar_Syntax_Syntax.lbname
                                           in
                                        FStar_Range.string_of_range
                                          uu____9316
                                         in
                                      let uu____9317 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      FStar_Util.print2
                                        "(%s) Checked type annotation %s\n"
                                        uu____9315 uu____9317
                                  | uu____9318 -> ());
                                 (let t = norm env1 t  in
                                  let uu____9320 =
                                    FStar_TypeChecker_Env.set_expected_typ
                                      env1 t
                                     in
                                  ((Some t), g, univ_vars, univ_opening,
                                    uu____9320)))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9325  ->
      match uu____9325 with
      | (x,imp) ->
          let uu____9336 = FStar_Syntax_Util.type_u ()  in
          (match uu____9336 with
           | (tu,u) ->
               ((let uu____9348 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 match uu____9348 with
                 | true  ->
                     let uu____9349 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____9350 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____9351 = FStar_Syntax_Print.term_to_string tu
                        in
                     FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                       uu____9349 uu____9350 uu____9351
                 | uu____9352 -> ());
                (let uu____9353 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____9353 with
                 | (t,uu____9364,g) ->
                     let x =
                       ((let uu___123_9369 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___123_9369.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___123_9369.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____9371 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       match uu____9371 with
                       | true  ->
                           let uu____9372 =
                             FStar_Syntax_Print.bv_to_string (Prims.fst x)
                              in
                           let uu____9373 =
                             FStar_Syntax_Print.term_to_string t  in
                           FStar_Util.print2 "Pushing binder %s at type %s\n"
                             uu____9372 uu____9373
                       | uu____9374 -> ());
                      (let uu____9375 = push_binding env x  in
                       (x, uu____9375, g, u))))))

and tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe Prims.list)
  =
  fun env  ->
    fun bs  ->
      let rec aux env bs =
        match bs with
        | [] -> ([], env, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs ->
            let uu____9426 = tc_binder env b  in
            (match uu____9426 with
             | (b,env',g,u) ->
                 let uu____9449 = aux env' bs  in
                 (match uu____9449 with
                  | (bs,env',g',us) ->
                      let uu____9478 =
                        let uu____9479 =
                          FStar_TypeChecker_Rel.close_guard [b] g'  in
                        FStar_TypeChecker_Rel.conj_guard g uu____9479  in
                      ((b :: bs), env', uu____9478, (u :: us))))
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
      let tc_args env args =
        FStar_List.fold_right
          (fun uu____9522  ->
             fun uu____9523  ->
               match (uu____9522, uu____9523) with
               | ((t,imp),(args,g)) ->
                   let uu____9560 = tc_term env t  in
                   (match uu____9560 with
                    | (t,uu____9570,g') ->
                        let uu____9572 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t, imp) :: args), uu____9572))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9590  ->
             match uu____9590 with
             | (pats,g) ->
                 let uu____9604 = tc_args env p  in
                 (match uu____9604 with
                  | (args,g') ->
                      let uu____9612 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats), uu____9612))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____9620 = tc_maybe_toplevel_term env e  in
      match uu____9620 with
      | (e,c,g) ->
          let uu____9630 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          (match uu____9630 with
           | true  -> (e, c, g)
           | uu____9634 ->
               let g = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                  in
               let c = c.FStar_Syntax_Syntax.comp ()  in
               let c = norm_c env c  in
               let uu____9640 =
                 let uu____9643 =
                   FStar_TypeChecker_Util.is_pure_effect env
                     (FStar_Syntax_Util.comp_effect_name c)
                    in
                 match uu____9643 with
                 | true  ->
                     let uu____9646 =
                       FStar_Syntax_Syntax.mk_Total
                         (FStar_Syntax_Util.comp_result c)
                        in
                     (uu____9646, false)
                 | uu____9647 ->
                     let uu____9648 =
                       FStar_Syntax_Syntax.mk_GTotal
                         (FStar_Syntax_Util.comp_result c)
                        in
                     (uu____9648, true)
                  in
               (match uu____9640 with
                | (target_comp,allow_ghost) ->
                    let uu____9654 =
                      FStar_TypeChecker_Rel.sub_comp env c target_comp  in
                    (match uu____9654 with
                     | Some g' ->
                         let uu____9660 =
                           FStar_TypeChecker_Rel.conj_guard g g'  in
                         (e, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                           uu____9660)
                     | uu____9661 ->
                         (match allow_ghost with
                          | true  ->
                              let uu____9666 =
                                let uu____9667 =
                                  let uu____9670 =
                                    FStar_TypeChecker_Err.expected_ghost_expression
                                      e c
                                     in
                                  (uu____9670, (e.FStar_Syntax_Syntax.pos))
                                   in
                                FStar_Errors.Error uu____9667  in
                              Prims.raise uu____9666
                          | uu____9674 ->
                              let uu____9675 =
                                let uu____9676 =
                                  let uu____9679 =
                                    FStar_TypeChecker_Err.expected_pure_expression
                                      e c
                                     in
                                  (uu____9679, (e.FStar_Syntax_Syntax.pos))
                                   in
                                FStar_Errors.Error uu____9676  in
                              Prims.raise uu____9675))))

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
        let env = FStar_TypeChecker_Env.set_expected_typ env t  in
        tc_tot_or_gtot_term env e

and tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun t  ->
      let uu____9692 = tc_tot_or_gtot_term env t  in
      match uu____9692 with
      | (t,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; (t, c))

let type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      (let uu____9712 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       match uu____9712 with
       | true  ->
           let uu____9713 = FStar_Syntax_Print.term_to_string e  in
           FStar_Util.print1 "Checking term %s\n" uu____9713
       | uu____9714 -> ());
      (let env =
         let uu___124_9716 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___124_9716.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___124_9716.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___124_9716.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___124_9716.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___124_9716.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___124_9716.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___124_9716.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___124_9716.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___124_9716.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___124_9716.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___124_9716.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___124_9716.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___124_9716.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___124_9716.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___124_9716.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___124_9716.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___124_9716.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___124_9716.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___124_9716.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___124_9716.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___124_9716.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___124_9716.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___124_9716.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____9717 =
         FStar_All.try_with
           (fun uu___126_9724  ->
              match () with | () -> tc_tot_or_gtot_term env e)
           (fun uu___125_9728  ->
              match uu___125_9728 with
              | FStar_Errors.Error (msg,uu____9733) ->
                  let uu____9734 =
                    let uu____9735 =
                      let uu____9738 = FStar_TypeChecker_Env.get_range env
                         in
                      ((Prims.strcat "Implicit argument: " msg), uu____9738)
                       in
                    FStar_Errors.Error uu____9735  in
                  Prims.raise uu____9734)
          in
       match uu____9717 with
       | (t,c,g) ->
           let uu____9748 = FStar_Syntax_Util.is_total_lcomp c  in
           (match uu____9748 with
            | true  -> (t, (c.FStar_Syntax_Syntax.res_typ), g)
            | uu____9754 ->
                let uu____9755 =
                  let uu____9756 =
                    let uu____9759 =
                      let uu____9760 = FStar_Syntax_Print.term_to_string e
                         in
                      FStar_Util.format1
                        "Implicit argument: Expected a total term; got a ghost term: %s"
                        uu____9760
                       in
                    let uu____9761 = FStar_TypeChecker_Env.get_range env  in
                    (uu____9759, uu____9761)  in
                  FStar_Errors.Error uu____9756  in
                Prims.raise uu____9755))
  
let level_of_type_fail env e t =
  let uu____9782 =
    let uu____9783 =
      let uu____9786 =
        let uu____9787 = FStar_Syntax_Print.term_to_string e  in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____9787 t
         in
      let uu____9788 = FStar_TypeChecker_Env.get_range env  in
      (uu____9786, uu____9788)  in
    FStar_Errors.Error uu____9783  in
  Prims.raise uu____9782 
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t =
          let uu____9805 =
            let uu____9806 = FStar_Syntax_Util.unrefine t  in
            uu____9806.FStar_Syntax_Syntax.n  in
          match uu____9805 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____9810 ->
              (match retry with
               | true  ->
                   let t =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env t
                      in
                   aux false t
               | uu____9812 ->
                   let uu____9813 = FStar_Syntax_Util.type_u ()  in
                   (match uu____9813 with
                    | (t_u,u) ->
                        let env =
                          let uu___127_9819 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___127_9819.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___127_9819.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___127_9819.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___127_9819.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___127_9819.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___127_9819.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___127_9819.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___127_9819.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___127_9819.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___127_9819.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___127_9819.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___127_9819.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___127_9819.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___127_9819.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___127_9819.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___127_9819.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___127_9819.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___127_9819.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___127_9819.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.type_of =
                              (uu___127_9819.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___127_9819.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___127_9819.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qname_and_index =
                              (uu___127_9819.FStar_TypeChecker_Env.qname_and_index)
                          }  in
                        let g = FStar_TypeChecker_Rel.teq env t t_u  in
                        ((match g.FStar_TypeChecker_Env.guard_f with
                          | FStar_TypeChecker_Common.NonTrivial f ->
                              let uu____9823 =
                                FStar_Syntax_Print.term_to_string t  in
                              level_of_type_fail env e uu____9823
                          | uu____9824 ->
                              FStar_TypeChecker_Rel.force_trivial_guard env g);
                         u)))
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
      let uu____9833 =
        let uu____9834 = FStar_Syntax_Subst.compress e  in
        uu____9834.FStar_Syntax_Syntax.n  in
      match uu____9833 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____9843 ->
          let e = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____9854) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____9879,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____9894) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9901 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9901 with | (uu____9910,t) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____9912,FStar_Util.Inl t,uu____9914) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____9933,FStar_Util.Inr c,uu____9935) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____9965;
             FStar_Syntax_Syntax.pos = uu____9966;
             FStar_Syntax_Syntax.vars = uu____9967;_},us)
          ->
          let uu____9973 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9973 with
           | (us',t) ->
               ((match (FStar_List.length us) <> (FStar_List.length us') with
                 | true  ->
                     let uu____9989 =
                       let uu____9990 =
                         let uu____9993 = FStar_TypeChecker_Env.get_range env
                            in
                         ("Unexpected number of universe instantiations",
                           uu____9993)
                          in
                       FStar_Errors.Error uu____9990  in
                     Prims.raise uu____9989
                 | uu____9994 ->
                     FStar_List.iter2
                       (fun u'  ->
                          fun u  ->
                            match u' with
                            | FStar_Syntax_Syntax.U_unif u'' ->
                                FStar_Unionfind.change u'' (Some u)
                            | uu____10001 -> failwith "Impossible") us' us);
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10002 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10010) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10027 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____10027 with
           | (bs,c) ->
               let us =
                 FStar_List.map
                   (fun uu____10038  ->
                      match uu____10038 with
                      | (b,uu____10042) ->
                          let uu____10043 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10043) bs
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c  in
                 let uu____10048 = universe_of_aux env res  in
                 level_of_type env res uu____10048  in
               let u_c =
                 let uu____10050 =
                   FStar_TypeChecker_Util.effect_repr env c u_res  in
                 match uu____10050 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____10053 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____10053
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)) None
                 e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let rec type_of_head retry hd args =
            let hd = FStar_Syntax_Subst.compress hd  in
            match hd.FStar_Syntax_Syntax.n with
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
                let uu____10139 = universe_of_aux env hd  in
                (uu____10139, args)
            | FStar_Syntax_Syntax.Tm_match (uu____10149,hd::uu____10151) ->
                let uu____10198 = FStar_Syntax_Subst.open_branch hd  in
                (match uu____10198 with
                 | (uu____10208,uu____10209,hd) ->
                     let uu____10225 = FStar_Syntax_Util.head_and_args hd  in
                     (match uu____10225 with
                      | (hd,args) -> type_of_head retry hd args))
            | uu____10260 when retry ->
                let e =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____10262 = FStar_Syntax_Util.head_and_args e  in
                (match uu____10262 with
                 | (hd,args) -> type_of_head false hd args)
            | uu____10297 ->
                let uu____10298 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____10298 with
                 | (env,uu____10312) ->
                     let env =
                       let uu___128_10316 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___128_10316.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___128_10316.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___128_10316.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___128_10316.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___128_10316.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___128_10316.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___128_10316.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___128_10316.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___128_10316.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___128_10316.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___128_10316.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___128_10316.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___128_10316.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___128_10316.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___128_10316.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___128_10316.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___128_10316.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___128_10316.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___128_10316.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___128_10316.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___128_10316.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     ((let uu____10318 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "UniverseOf")
                          in
                       match uu____10318 with
                       | true  ->
                           let uu____10319 =
                             let uu____10320 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Range.string_of_range uu____10320  in
                           let uu____10321 =
                             FStar_Syntax_Print.term_to_string hd  in
                           FStar_Util.print2 "%s: About to type-check %s\n"
                             uu____10319 uu____10321
                       | uu____10322 -> ());
                      (let uu____10323 = tc_term env hd  in
                       match uu____10323 with
                       | (uu____10336,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10337;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10339;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10340;_},g)
                           ->
                           ((let uu____10350 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env g
                                in
                             FStar_All.pipe_right uu____10350 Prims.ignore);
                            (t, args)))))
             in
          let uu____10358 = type_of_head true hd args  in
          (match uu____10358 with
           | (t,args) ->
               let t =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____10387 = FStar_Syntax_Util.arrow_formals_comp t  in
               (match uu____10387 with
                | (bs,res) ->
                    let res = FStar_Syntax_Util.comp_result res  in
                    (match (FStar_List.length bs) = (FStar_List.length args)
                     with
                     | true  ->
                         let subst = FStar_Syntax_Util.subst_of_list bs args
                            in
                         FStar_Syntax_Subst.subst subst res
                     | uu____10419 ->
                         let uu____10420 =
                           FStar_Syntax_Print.term_to_string res  in
                         level_of_type_fail env e uu____10420)))
      | FStar_Syntax_Syntax.Tm_match (uu____10423,hd::uu____10425) ->
          let uu____10472 = FStar_Syntax_Subst.open_branch hd  in
          (match uu____10472 with
           | (uu____10475,uu____10476,hd) -> universe_of_aux env hd)
      | FStar_Syntax_Syntax.Tm_match (uu____10492,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____10526 = universe_of_aux env e  in
      level_of_type env e uu____10526
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____10539 = tc_binders env tps  in
      match uu____10539 with
      | (tps,env,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (tps, env, us))
  