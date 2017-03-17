open Prims
let instantiate_both : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___81_4 = env  in
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
  
let no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___82_8 = env  in
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
             match tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange with
             | true  -> v.FStar_Syntax_Syntax.pos
             | uu____33 ->
                 FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos
                   tl.FStar_Syntax_Syntax.pos
              in
           (let _0_240 =
              let _0_239 = FStar_Syntax_Syntax.as_arg v  in
              let _0_238 =
                let _0_237 = FStar_Syntax_Syntax.as_arg tl  in [_0_237]  in
              _0_239 :: _0_238  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _0_240)
             (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r) vs
      FStar_Syntax_Util.lex_top
  
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.bool =
  fun uu___76_41  ->
    match uu___76_41 with
    | Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____43 -> false
  
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
            | uu____94 ->
                let t =
                  match try_norm with | true  -> norm env t | uu____97 -> t
                   in
                let fvs' = FStar_Syntax_Free.names t  in
                let uu____100 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____100 with
                 | None  -> t
                 | Some x ->
                     (match Prims.op_Negation try_norm with
                      | true  -> aux true t
                      | uu____104 ->
                          let fail uu____108 =
                            let msg =
                              match head_opt with
                              | None  ->
                                  let _0_241 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  FStar_Util.format1
                                    "Bound variables '%s' escapes; add a type annotation"
                                    _0_241
                              | Some head ->
                                  let _0_243 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let _0_242 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env head
                                     in
                                  FStar_Util.format2
                                    "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                    _0_243 _0_242
                               in
                            Prims.raise
                              (FStar_Errors.Error
                                 (let _0_244 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  (msg, _0_244)))
                             in
                          let s =
                            let _0_246 =
                              let _0_245 = FStar_Syntax_Util.type_u ()  in
                              FStar_All.pipe_left Prims.fst _0_245  in
                            FStar_TypeChecker_Util.new_uvar env _0_246  in
                          let uu____114 =
                            FStar_TypeChecker_Rel.try_teq env t s  in
                          (match uu____114 with
                           | Some g ->
                               (FStar_TypeChecker_Rel.force_trivial_guard env
                                  g;
                                s)
                           | uu____118 -> fail ())))
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
        let uu____149 = FStar_Syntax_Syntax.is_null_binder b  in
        match uu____149 with
        | true  -> s
        | uu____150 -> (FStar_Syntax_Syntax.NT ((Prims.fst b), v)) :: s
  
let set_lcomp_result :
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___83_163 = lc  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___88_181.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___88_181.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____164  ->
             let _0_247 = lc.FStar_Syntax_Syntax.comp ()  in
             FStar_Syntax_Util.set_result_typ _0_247 t)
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
            let uu____201 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            match uu____201 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____202,c) ->
                let uu____214 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                (match uu____214 with
                 | true  ->
                     let t =
                       FStar_All.pipe_left FStar_Syntax_Util.unrefine
                         (FStar_Syntax_Util.comp_result c)
                        in
                     let uu____216 =
                       (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                        in
                     (match uu____216 with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Syntax_Const.unit_lid
                          -> false
                      | FStar_Syntax_Syntax.Tm_constant uu____218 -> false
                      | uu____219 -> true)
                 | uu____220 -> false)
            | uu____221 -> true  in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                FStar_Syntax_Util.lcomp_of_comp
                  (let uu____224 =
                     (Prims.op_Negation (should_return t)) ||
                       (Prims.op_Negation
                          (FStar_TypeChecker_Env.should_verify env))
                      in
                   match uu____224 with
                   | true  -> FStar_Syntax_Syntax.mk_Total t
                   | uu____227 -> FStar_TypeChecker_Util.return_value env t e)
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____232 =
            let uu____236 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____236 with
            | None  -> let _0_248 = memo_tk e t  in (_0_248, lc, guard)
            | Some t' ->
                ((let uu____243 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High  in
                  match uu____243 with
                  | true  ->
                      let _0_250 = FStar_Syntax_Print.term_to_string t  in
                      let _0_249 = FStar_Syntax_Print.term_to_string t'  in
                      FStar_Util.print2
                        "Computed return type %s; expected type %s\n" _0_250
                        _0_249
                  | uu____244 -> ());
                 (let uu____245 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t'
                     in
                  match uu____245 with
                  | (e,lc) ->
                      let t = lc.FStar_Syntax_Syntax.res_typ  in
                      let uu____256 =
                        FStar_TypeChecker_Util.check_and_ascribe env e t t'
                         in
                      (match uu____256 with
                       | (e,g) ->
                           ((let uu____265 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             match uu____265 with
                             | true  ->
                                 let _0_254 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 let _0_253 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 let _0_252 =
                                   FStar_TypeChecker_Rel.guard_to_string env
                                     g
                                    in
                                 let _0_251 =
                                   FStar_TypeChecker_Rel.guard_to_string env
                                     guard
                                    in
                                 FStar_Util.print4
                                   "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                   _0_254 _0_253 _0_252 _0_251
                             | uu____266 -> ());
                            (let msg =
                               let uu____271 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               match uu____271 with
                               | true  -> None
                               | uu____277 ->
                                   FStar_All.pipe_left
                                     (fun _0_255  -> Some _0_255)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env t t')
                                in
                             let g = FStar_TypeChecker_Rel.conj_guard g guard
                                in
                             let uu____286 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e lc g
                                in
                             match uu____286 with
                             | (lc,g) ->
                                 let _0_256 = memo_tk e t'  in
                                 (_0_256, (set_lcomp_result lc t'), g))))))
             in
          match uu____232 with
          | (e,lc,g) ->
              ((let uu____301 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                match uu____301 with
                | true  ->
                    let _0_257 = FStar_Syntax_Print.lcomp_to_string lc  in
                    FStar_Util.print1 "Return comp type is %s\n" _0_257
                | uu____302 -> ());
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
        let uu____318 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____318 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____324 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____324 with
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
                         (Prims.op_Negation
                            (FStar_Syntax_Util.is_pure_or_ghost_comp c)))
                     in
                  (match uu____362 with
                   | true  ->
                       Some
                         (FStar_Syntax_Util.ml_comp
                            (FStar_Syntax_Util.comp_result c)
                            e.FStar_Syntax_Syntax.pos)
                   | uu____364 ->
                       let uu____365 =
                         FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                       (match uu____365 with
                        | true  -> None
                        | uu____367 ->
                            let uu____368 = FStar_Syntax_Util.is_pure_comp c
                               in
                            (match uu____368 with
                             | true  ->
                                 Some
                                   (FStar_Syntax_Syntax.mk_Total
                                      (FStar_Syntax_Util.comp_result c))
                             | uu____370 ->
                                 let uu____371 =
                                   FStar_Syntax_Util.is_pure_or_ghost_comp c
                                    in
                                 (match uu____371 with
                                  | true  ->
                                      Some
                                        (FStar_Syntax_Syntax.mk_GTotal
                                           (FStar_Syntax_Util.comp_result c))
                                  | uu____373 -> None))))
               in
            (match expected_c_opt with
             | None  ->
                 let _0_258 = norm_c env c  in
                 (e, _0_258, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____379 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                   match uu____379 with
                   | true  ->
                       let _0_261 = FStar_Syntax_Print.term_to_string e  in
                       let _0_260 = FStar_Syntax_Print.comp_to_string c  in
                       let _0_259 =
                         FStar_Syntax_Print.comp_to_string expected_c  in
                       FStar_Util.print3
                         "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                         _0_261 _0_260 _0_259
                   | uu____380 -> ());
                  (let c = norm_c env c  in
                   (let uu____383 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                    match uu____383 with
                    | true  ->
                        let _0_264 = FStar_Syntax_Print.term_to_string e  in
                        let _0_263 = FStar_Syntax_Print.comp_to_string c  in
                        let _0_262 =
                          FStar_Syntax_Print.comp_to_string expected_c  in
                        FStar_Util.print3
                          "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                          _0_264 _0_263 _0_262
                    | uu____384 -> ());
                   (let uu____385 =
                      FStar_TypeChecker_Util.check_comp env e c expected_c
                       in
                    match uu____385 with
                    | (e,uu____393,g) ->
                        let g =
                          let _0_265 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_TypeChecker_Util.label_guard _0_265
                            "could not prove post-condition" g
                           in
                        ((let uu____397 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low
                             in
                          match uu____397 with
                          | true  ->
                              let _0_267 =
                                FStar_Range.string_of_range
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let _0_266 =
                                FStar_TypeChecker_Rel.guard_to_string env g
                                 in
                              FStar_Util.print2
                                "(%s) DONE check_expected_effect; guard is: %s\n"
                                _0_267 _0_266
                          | uu____398 -> ());
                         (let e =
                            FStar_TypeChecker_Util.maybe_lift env e
                              (FStar_Syntax_Util.comp_effect_name c)
                              (FStar_Syntax_Util.comp_effect_name expected_c)
                              (FStar_Syntax_Util.comp_result c)
                             in
                          (e, expected_c, g)))))))
  
let no_logical_guard env uu____419 =
  match uu____419 with
  | (te,kt,f) ->
      let uu____426 = FStar_TypeChecker_Rel.guard_form f  in
      (match uu____426 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f ->
           Prims.raise
             (FStar_Errors.Error
                (let _0_269 =
                   FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                     env f
                    in
                 let _0_268 = FStar_TypeChecker_Env.get_range env  in
                 (_0_269, _0_268))))
  
let print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____437 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____437 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let _0_270 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" _0_270
  
let check_smt_pat env t bs c =
  let uu____474 = FStar_Syntax_Util.is_smt_lemma t  in
  match uu____474 with
  | true  ->
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Comp
           { FStar_Syntax_Syntax.comp_univs = uu____475;
             FStar_Syntax_Syntax.effect_name = uu____476;
             FStar_Syntax_Syntax.result_typ = uu____477;
             FStar_Syntax_Syntax.effect_args =
               _pre::_post::(pats,uu____481)::[];
             FStar_Syntax_Syntax.flags = uu____482;_}
           ->
           let pat_vars =
             FStar_Syntax_Free.names
               (FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.Beta] env pats)
              in
           let uu____516 =
             FStar_All.pipe_right bs
               (FStar_Util.find_opt
                  (fun uu____528  ->
                     match uu____528 with
                     | (b,uu____532) ->
                         Prims.op_Negation (FStar_Util.set_mem b pat_vars)))
              in
           (match uu____516 with
            | None  -> ()
            | Some (x,uu____536) ->
                let _0_272 =
                  let _0_271 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s" _0_271
                   in
                FStar_Errors.warn t.FStar_Syntax_Syntax.pos _0_272)
       | uu____539 -> failwith "Impossible")
  | uu____540 -> () 
let guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____560 =
          Prims.op_Negation (FStar_TypeChecker_Env.should_verify env)  in
        match uu____560 with
        | true  -> env.FStar_TypeChecker_Env.letrecs
        | uu____564 ->
            (match env.FStar_TypeChecker_Env.letrecs with
             | [] -> []
             | letrecs ->
                 let r = FStar_TypeChecker_Env.get_range env  in
                 let env =
                   let uu___84_578 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___84_578.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___84_578.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___84_578.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___84_578.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___84_578.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___84_578.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___84_578.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___84_578.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___84_578.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___84_578.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___84_578.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___84_578.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs = [];
                     FStar_TypeChecker_Env.top_level =
                       (uu___84_578.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___84_578.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___84_578.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___84_578.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___84_578.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax =
                       (uu___84_578.FStar_TypeChecker_Env.lax);
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___84_578.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.type_of =
                       (uu___84_578.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___84_578.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___84_578.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qname_and_index =
                       (uu___84_578.FStar_TypeChecker_Env.qname_and_index)
                   }  in
                 let precedes =
                   FStar_TypeChecker_Util.fvar_const env
                     FStar_Syntax_Const.precedes_lid
                    in
                 let decreases_clause bs c =
                   let filter_types_and_functions bs =
                     FStar_All.pipe_right bs
                       (FStar_List.collect
                          (fun uu____601  ->
                             match uu____601 with
                             | (b,uu____606) ->
                                 let t =
                                   let _0_273 =
                                     FStar_Syntax_Util.unrefine
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   unfold_whnf env _0_273  in
                                 (match t.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_type _
                                    |FStar_Syntax_Syntax.Tm_arrow _ -> []
                                  | uu____611 ->
                                      let _0_274 =
                                        FStar_Syntax_Syntax.bv_to_name b  in
                                      [_0_274])))
                      in
                   let as_lex_list dec =
                     let uu____616 = FStar_Syntax_Util.head_and_args dec  in
                     match uu____616 with
                     | (head,uu____627) ->
                         (match head.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.lexcons_lid
                              -> dec
                          | uu____643 -> mk_lex_list [dec])
                      in
                   let cflags = FStar_Syntax_Util.comp_flags c  in
                   let uu____646 =
                     FStar_All.pipe_right cflags
                       (FStar_List.tryFind
                          (fun uu___77_650  ->
                             match uu___77_650 with
                             | FStar_Syntax_Syntax.DECREASES uu____651 ->
                                 true
                             | uu____654 -> false))
                      in
                   match uu____646 with
                   | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                       as_lex_list dec
                   | uu____658 ->
                       let xs =
                         FStar_All.pipe_right bs filter_types_and_functions
                          in
                       (match xs with
                        | x::[] -> x
                        | uu____664 -> mk_lex_list xs)
                    in
                 let previous_dec = decreases_clause actuals expected_c  in
                 let guard_one_letrec uu____676 =
                   match uu____676 with
                   | (l,t) ->
                       let uu____685 =
                         (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                          in
                       (match uu____685 with
                        | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                            let formals =
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____716  ->
                                      match uu____716 with
                                      | (x,imp) ->
                                          let uu____723 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          (match uu____723 with
                                           | true  ->
                                               let _0_276 =
                                                 let _0_275 =
                                                   Some
                                                     (FStar_Syntax_Syntax.range_of_bv
                                                        x)
                                                    in
                                                 FStar_Syntax_Syntax.new_bv
                                                   _0_275
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               (_0_276, imp)
                                           | uu____726 -> (x, imp))))
                               in
                            let uu____727 =
                              FStar_Syntax_Subst.open_comp formals c  in
                            (match uu____727 with
                             | (formals,c) ->
                                 let dec = decreases_clause formals c  in
                                 let precedes =
                                   (let _0_280 =
                                      let _0_279 =
                                        FStar_Syntax_Syntax.as_arg dec  in
                                      let _0_278 =
                                        let _0_277 =
                                          FStar_Syntax_Syntax.as_arg
                                            previous_dec
                                           in
                                        [_0_277]  in
                                      _0_279 :: _0_278  in
                                    FStar_Syntax_Syntax.mk_Tm_app precedes
                                      _0_280) None r
                                    in
                                 let uu____744 = FStar_Util.prefix formals
                                    in
                                 (match uu____744 with
                                  | (bs,(last,imp)) ->
                                      let last =
                                        let uu___85_770 = last  in
                                        let _0_281 =
                                          FStar_Syntax_Util.refine last
                                            precedes
                                           in
                                        {
                                          FStar_Syntax_Syntax.ppname =
                                            (uu___85_770.FStar_Syntax_Syntax.ppname);
                                          FStar_Syntax_Syntax.index =
                                            (uu___85_770.FStar_Syntax_Syntax.index);
                                          FStar_Syntax_Syntax.sort = _0_281
                                        }  in
                                      let refined_formals =
                                        FStar_List.append bs [(last, imp)]
                                         in
                                      let t' =
                                        FStar_Syntax_Util.arrow
                                          refined_formals c
                                         in
                                      ((let uu____785 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Low
                                           in
                                        match uu____785 with
                                        | true  ->
                                            let _0_284 =
                                              FStar_Syntax_Print.lbname_to_string
                                                l
                                               in
                                            let _0_283 =
                                              FStar_Syntax_Print.term_to_string
                                                t
                                               in
                                            let _0_282 =
                                              FStar_Syntax_Print.term_to_string
                                                t'
                                               in
                                            FStar_Util.print3
                                              "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                              _0_284 _0_283 _0_282
                                        | uu____786 -> ());
                                       (l, t'))))
                        | uu____789 ->
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
        (let uu___86_1053 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___91_1149.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___91_1149.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___91_1149.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___91_1149.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___91_1149.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___91_1149.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___91_1149.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___91_1149.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___91_1149.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___91_1149.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___91_1149.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___91_1149.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___91_1149.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___91_1149.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___91_1149.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___91_1149.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___91_1149.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___91_1149.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___91_1149.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___91_1149.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___91_1149.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___91_1149.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___91_1149.FStar_TypeChecker_Env.qname_and_index)
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
        | uu____1060 ->
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      (let uu____1062 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       match uu____1062 with
       | true  ->
           let _0_287 =
             let _0_285 = FStar_TypeChecker_Env.get_range env  in
             FStar_All.pipe_left FStar_Range.string_of_range _0_285  in
           let _0_286 = FStar_Syntax_Print.tag_of_term e  in
           FStar_Util.print2 "%s (%s)\n" _0_287 _0_286
       | uu____1063 -> ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1167 -> failwith "Impossible"
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
           let uu____1107 = tc_tot_or_gtot_term env e  in
           (match uu____1107 with
            | (e,c,g) ->
                let g =
                  let uu___87_1118 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___92_1217.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___92_1217.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___87_1118.FStar_TypeChecker_Env.implicits)
                  }  in
                (e, c, g))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1131 = FStar_Syntax_Util.type_u ()  in
           (match uu____1131 with
            | (t,u) ->
                let uu____1139 = tc_check_tot_or_gtot_term env e t  in
                (match uu____1139 with
                 | (e,c,g) ->
                     let uu____1149 =
                       let uu____1158 =
                         FStar_TypeChecker_Env.clear_expected_typ env  in
                       match uu____1158 with
                       | (env,uu____1171) -> tc_pats env pats  in
                     (match uu____1149 with
                      | (pats,g') ->
                          let g' =
                            let uu___88_1192 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___93_1291.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___93_1291.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___88_1192.FStar_TypeChecker_Env.implicits)
                            }  in
                          let _0_289 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let _0_288 = FStar_TypeChecker_Rel.conj_guard g g'
                             in
                          (_0_289, c, _0_288))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1212 =
             (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n  in
           (match uu____1212 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1318,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1320;
                               FStar_Syntax_Syntax.lbtyp = uu____1321;
                               FStar_Syntax_Syntax.lbeff = uu____1322;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1238 =
                  let _0_290 =
                    FStar_TypeChecker_Env.set_expected_typ env
                      FStar_TypeChecker_Common.t_unit
                     in
                  tc_term _0_290 e1  in
                (match uu____1238 with
                 | (e1,c1,g1) ->
                     let uu____1248 = tc_term env e2  in
                     (match uu____1248 with
                      | (e2,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind
                              e1.FStar_Syntax_Syntax.pos env (Some e1) c1
                              (None, c2)
                             in
                          let e =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_let
                                  (let _0_293 =
                                     let _0_292 =
                                       let _0_291 =
                                         FStar_Syntax_Syntax.mk_lb
                                           (x, [],
                                             (c1.FStar_Syntax_Syntax.eff_name),
                                             FStar_TypeChecker_Common.t_unit,
                                             e1)
                                          in
                                       [_0_291]  in
                                     (false, _0_292)  in
                                   (_0_293, e2))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e4,
                                    (FStar_Syntax_Syntax.Meta_desugared
                                       FStar_Syntax_Syntax.Sequence))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let _0_294 = FStar_TypeChecker_Rel.conj_guard g1 g2
                             in
                          (e, c, _0_294)))
            | uu____1295 ->
                let uu____1296 = tc_term env e  in
                (match uu____1296 with
                 | (e,c,g) ->
                     let e =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (e2,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Sequence))))
                         (Some
                            ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_monadic uu____1320) -> tc_term env e
       | FStar_Syntax_Syntax.Tm_meta (e,m) ->
           let uu____1335 = tc_term env e  in
           (match uu____1335 with
            | (e,c,g) ->
                let e =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos
                   in
                (e, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e,FStar_Util.Inr expected_c,uu____1360) ->
           let uu____1379 = FStar_TypeChecker_Env.clear_expected_typ env  in
           (match uu____1379 with
            | (env0,uu____1387) ->
                let uu____1390 = tc_comp env0 expected_c  in
                (match uu____1390 with
                 | (expected_c,uu____1398,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c  in
                     let uu____1403 =
                       let _0_295 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term _0_295 e  in
                     (match uu____1403 with
                      | (e,c',g') ->
                          let uu____1413 =
                            let _0_297 =
                              let _0_296 = c'.FStar_Syntax_Syntax.comp ()  in
                              (e, _0_296)  in
                            check_expected_effect env0 (Some expected_c)
                              _0_297
                             in
                          (match uu____1413 with
                           | (e,expected_c,g'') ->
                               let e =
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
                                 FStar_Syntax_Util.lcomp_of_comp expected_c
                                  in
                               let f =
                                 let _0_298 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g _0_298
                                  in
                               let uu____1449 =
                                 comp_check_expected_typ env e lc  in
                               (match uu____1449 with
                                | (e,c,f2) ->
                                    let _0_299 =
                                      FStar_TypeChecker_Rel.conj_guard f f2
                                       in
                                    (e, c, _0_299))))))
       | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t,uu____1461) ->
           let uu____1480 = FStar_Syntax_Util.type_u ()  in
           (match uu____1480 with
            | (k,u) ->
                let uu____1488 = tc_check_tot_or_gtot_term env t k  in
                (match uu____1488 with
                 | (t,uu____1496,f) ->
                     let uu____1498 =
                       let _0_300 =
                         FStar_TypeChecker_Env.set_expected_typ env t  in
                       tc_term _0_300 e  in
                     (match uu____1498 with
                      | (e,c,g) ->
                          let uu____1508 =
                            let _0_301 =
                              FStar_TypeChecker_Env.set_range env
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1704  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              _0_301 e c f
                             in
                          (match uu____1508 with
                           | (c,f) ->
                               let uu____1519 =
                                 let _0_302 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, ((FStar_Util.Inl t1), None),
                                           (Some
                                              (c.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env _0_302 c  in
                               (match uu____1519 with
                                | (e,c,f2) ->
                                    let _0_304 =
                                      let _0_303 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f
                                        _0_303
                                       in
                                    (e, c, _0_304))))))
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
           let rest = hd :: rest  in
           let uu____1624 = FStar_Syntax_Util.head_and_args top  in
           (match uu____1624 with
            | (unary_op,uu____1638) ->
                let head =
                  let _0_305 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (Prims.fst a).FStar_Syntax_Syntax.pos
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    _0_305
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
              FStar_Syntax_Syntax.tk = uu____1904;
              FStar_Syntax_Syntax.pos = uu____1905;
              FStar_Syntax_Syntax.vars = uu____1906;_},(e1,aqual)::[])
           ->
           ((match FStar_Option.isSome aqual with
             | true  ->
                 FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "Qualifier on argument to reify is irrelevant and will be ignored"
             | uu____1726 -> ());
            (let uu____1727 =
               let uu____1731 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               match uu____1731 with | (env0,uu____1739) -> tc_term env0 e
                in
             match uu____1727 with
             | (e,c,g) ->
                 let uu____1748 = FStar_Syntax_Util.head_and_args top  in
                 (match uu____1748 with
                  | (reify_op,uu____1762) ->
                      let u_c =
                        let uu____1778 =
                          tc_term env c.FStar_Syntax_Syntax.res_typ  in
                        match uu____1778 with
                        | (uu____1782,c,uu____1784) ->
                            let uu____1785 =
                              (FStar_Syntax_Subst.compress
                                 c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
                               in
                            (match uu____1785 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____1787 ->
                                 failwith
                                   "Unexpected result type of computation")
                         in
                      let repr = FStar_TypeChecker_Util.reify_comp env c u_c
                         in
                      let e =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos
                         in
                      let c =
                        let _0_306 = FStar_Syntax_Syntax.mk_Total repr  in
                        FStar_All.pipe_right _0_306
                          FStar_Syntax_Util.lcomp_of_comp
                         in
                      let uu____1810 = comp_check_expected_typ env e c  in
                      (match uu____1810 with
                       | (e,c,g') ->
                           let _0_307 = FStar_TypeChecker_Rel.conj_guard g g'
                              in
                           (e, c, _0_307)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2045;
              FStar_Syntax_Syntax.pos = uu____2046;
              FStar_Syntax_Syntax.vars = uu____2047;_},(e1,aqual)::[])
           ->
           ((match FStar_Option.isSome aqual with
             | true  ->
                 FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "Qualifier on argument to reflect is irrelevant and will be ignored"
             | uu____1848 -> ());
            (let no_reflect uu____1855 =
               Prims.raise
                 (FStar_Errors.Error
                    (let _0_308 =
                       FStar_Util.format1 "Effect %s cannot be reified"
                         l.FStar_Ident.str
                        in
                     (_0_308, (e.FStar_Syntax_Syntax.pos))))
                in
             let uu____1859 = FStar_Syntax_Util.head_and_args top  in
             match uu____1859 with
             | (reflect_op,uu____1873) ->
                 let uu____1888 = FStar_TypeChecker_Env.effect_decl_opt env l
                    in
                 (match uu____1888 with
                  | None  -> no_reflect ()
                  | Some ed ->
                      let uu____1894 =
                        Prims.op_Negation
                          (FStar_All.pipe_right
                             ed.FStar_Syntax_Syntax.qualifiers
                             FStar_Syntax_Syntax.contains_reflectable)
                         in
                      (match uu____1894 with
                       | true  -> no_reflect ()
                       | uu____1899 ->
                           let uu____1900 =
                             FStar_TypeChecker_Env.clear_expected_typ env  in
                           (match uu____1900 with
                            | (env_no_ex,topt) ->
                                let uu____1911 =
                                  let u = FStar_TypeChecker_Env.new_u_univ ()
                                     in
                                  let repr =
                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                      [u] env ed
                                      ([], (ed.FStar_Syntax_Syntax.repr))
                                     in
                                  let t =
                                    (FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_app
                                          (let _0_312 =
                                             let _0_311 =
                                               FStar_Syntax_Syntax.as_arg
                                                 FStar_Syntax_Syntax.tun
                                                in
                                             let _0_310 =
                                               let _0_309 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   FStar_Syntax_Syntax.tun
                                                  in
                                               [_0_309]  in
                                             _0_311 :: _0_310  in
                                           (repr, _0_312)))) None
                                      top.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____1935 =
                                    let _0_314 =
                                      let _0_313 =
                                        FStar_TypeChecker_Env.clear_expected_typ
                                          env
                                         in
                                      FStar_All.pipe_right _0_313 Prims.fst
                                       in
                                    tc_tot_or_gtot_term _0_314 t  in
                                  match uu____1935 with
                                  | (t,uu____1952,g) ->
                                      let uu____1954 =
                                        (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                         in
                                      (match uu____1954 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____1963,(res,uu____1965)::
                                            (wp,uu____1967)::[])
                                           -> (t, res, wp, g)
                                       | uu____2001 -> failwith "Impossible")
                                   in
                                (match uu____1911 with
                                 | (expected_repr_typ,res_typ,wp,g0) ->
                                     let uu____2025 =
                                       let uu____2028 =
                                         tc_tot_or_gtot_term env_no_ex e  in
                                       match uu____2028 with
                                       | (e,c,g) ->
                                           ((let uu____2038 =
                                               let _0_315 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   c
                                                  in
                                               FStar_All.pipe_left
                                                 Prims.op_Negation _0_315
                                                in
                                             match uu____2038 with
                                             | true  ->
                                                 FStar_TypeChecker_Err.add_errors
                                                   env
                                                   [("Expected Tot, got a GTot computation",
                                                      (e.FStar_Syntax_Syntax.pos))]
                                             | uu____2043 -> ());
                                            (let uu____2044 =
                                               FStar_TypeChecker_Rel.try_teq
                                                 env_no_ex
                                                 c.FStar_Syntax_Syntax.res_typ
                                                 expected_repr_typ
                                                in
                                             match uu____2044 with
                                             | None  ->
                                                 ((let _0_320 =
                                                     let _0_319 =
                                                       let _0_318 =
                                                         let _0_317 =
                                                           FStar_Syntax_Print.term_to_string
                                                             ed.FStar_Syntax_Syntax.repr
                                                            in
                                                         let _0_316 =
                                                           FStar_Syntax_Print.term_to_string
                                                             c.FStar_Syntax_Syntax.res_typ
                                                            in
                                                         FStar_Util.format2
                                                           "Expected an instance of %s; got %s"
                                                           _0_317 _0_316
                                                          in
                                                       (_0_318,
                                                         (e.FStar_Syntax_Syntax.pos))
                                                        in
                                                     [_0_319]  in
                                                   FStar_TypeChecker_Err.add_errors
                                                     env _0_320);
                                                  (let _0_321 =
                                                     FStar_TypeChecker_Rel.conj_guard
                                                       g g0
                                                      in
                                                   (e, _0_321)))
                                             | Some g' ->
                                                 let _0_323 =
                                                   let _0_322 =
                                                     FStar_TypeChecker_Rel.conj_guard
                                                       g g0
                                                      in
                                                   FStar_TypeChecker_Rel.conj_guard
                                                     g' _0_322
                                                    in
                                                 (e, _0_323)))
                                        in
                                     (match uu____2025 with
                                      | (e,g) ->
                                          let c =
                                            let _0_328 =
                                              FStar_Syntax_Syntax.mk_Comp
                                                (let _0_327 =
                                                   let _0_324 =
                                                     env.FStar_TypeChecker_Env.universe_of
                                                       env res_typ
                                                      in
                                                   [_0_324]  in
                                                 let _0_326 =
                                                   let _0_325 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp
                                                      in
                                                   [_0_325]  in
                                                 {
                                                   FStar_Syntax_Syntax.comp_univs
                                                     = _0_327;
                                                   FStar_Syntax_Syntax.effect_name
                                                     =
                                                     (ed.FStar_Syntax_Syntax.mname);
                                                   FStar_Syntax_Syntax.result_typ
                                                     = res_typ;
                                                   FStar_Syntax_Syntax.effect_args
                                                     = _0_326;
                                                   FStar_Syntax_Syntax.flags
                                                     = []
                                                 })
                                               in
                                            FStar_All.pipe_right _0_328
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
                                          let uu____2080 =
                                            comp_check_expected_typ env e c
                                             in
                                          (match uu____2080 with
                                           | (e,c,g') ->
                                               let _0_329 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   g' g
                                                  in
                                               (e, c, _0_329)))))))))
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let env0 = env  in
           let env =
             let _0_331 =
               let _0_330 = FStar_TypeChecker_Env.clear_expected_typ env  in
               FStar_All.pipe_right _0_330 Prims.fst  in
             FStar_All.pipe_right _0_331 instantiate_both  in
           ((let uu____2113 =
               FStar_TypeChecker_Env.debug env FStar_Options.High  in
             match uu____2113 with
             | true  ->
                 let _0_333 =
                   FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos
                    in
                 let _0_332 = FStar_Syntax_Print.term_to_string top  in
                 FStar_Util.print2 "(%s) Checking app %s\n" _0_333 _0_332
             | uu____2114 -> ());
            (let uu____2115 = tc_term (no_inst env) head  in
             match uu____2115 with
             | (head,chead,g_head) ->
                 let uu____2125 =
                   let uu____2129 =
                     (Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head)
                      in
                   match uu____2129 with
                   | true  ->
                       let _0_334 = FStar_TypeChecker_Env.expected_typ env0
                          in
                       check_short_circuit_args env head chead g_head args
                         _0_334
                   | uu____2133 ->
                       let _0_335 = FStar_TypeChecker_Env.expected_typ env0
                          in
                       check_application_args env head chead g_head args
                         _0_335
                    in
                 (match uu____2125 with
                  | (e,c,g) ->
                      ((let uu____2141 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Extreme
                           in
                        match uu____2141 with
                        | true  ->
                            let _0_336 =
                              FStar_TypeChecker_Rel.print_pending_implicits g
                               in
                            FStar_Util.print1
                              "Introduced {%s} implicits in application\n"
                              _0_336
                        | uu____2142 -> ());
                       (let c =
                          let uu____2144 =
                            ((FStar_TypeChecker_Env.should_verify env) &&
                               (Prims.op_Negation
                                  (FStar_Syntax_Util.is_lcomp_partial_return
                                     c)))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                             in
                          match uu____2144 with
                          | true  ->
                              FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                env e c
                          | uu____2145 -> c  in
                        let uu____2146 = comp_check_expected_typ env0 e c  in
                        match uu____2146 with
                        | (e,c,g') ->
                            let gimp =
                              let uu____2157 =
                                (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                                 in
                              match uu____2157 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2159) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e, (c.FStar_Syntax_Syntax.res_typ),
                                      (head.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___89_2191 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___94_2491.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___94_2491.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___94_2491.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2216 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let _0_337 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g _0_337  in
                            ((let uu____2219 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              match uu____2219 with
                              | true  ->
                                  let _0_339 =
                                    FStar_Syntax_Print.term_to_string e  in
                                  let _0_338 =
                                    FStar_TypeChecker_Rel.guard_to_string env
                                      gres
                                     in
                                  FStar_Util.print2
                                    "Guard from application node %s is %s\n"
                                    _0_339 _0_338
                              | uu____2220 -> ());
                             (e, c, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2249 = FStar_TypeChecker_Env.clear_expected_typ env  in
           (match uu____2249 with
            | (env1,topt) ->
                let env1 = instantiate_both env1  in
                let uu____2261 = tc_term env1 e1  in
                (match uu____2261 with
                 | (e1,c1,g1) ->
                     let uu____2271 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2277 = FStar_Syntax_Util.type_u ()  in
                           (match uu____2277 with
                            | (k,uu____2283) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env k  in
                                let _0_340 =
                                  FStar_TypeChecker_Env.set_expected_typ env
                                    res_t
                                   in
                                (_0_340, res_t))
                        in
                     (match uu____2271 with
                      | (env_branches,res_t) ->
                          ((let uu____2291 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            match uu____2291 with
                            | true  ->
                                let _0_341 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                FStar_Util.print1
                                  "Tm_match: expected type of branches is %s\n"
                                  _0_341
                            | uu____2292 -> ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e1.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____2342 =
                              let uu____2345 =
                                FStar_List.fold_right
                                  (fun uu____2669  ->
                                     fun uu____2670  ->
                                       match (uu____2669, uu____2670) with
                                       | ((uu____2702,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2735 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), _0_342))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____2345 with
                              | (cases,g) ->
                                  let _0_343 =
                                    FStar_TypeChecker_Util.bind_cases env
                                      res_t cases
                                     in
                                  (_0_343, g)
                               in
                            match uu____2342 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e1.FStar_Syntax_Syntax.pos env (Some e1)
                                    c1 ((Some guard_x), c_branches)
                                   in
                                let e =
                                  let mk_match scrutinee =
                                    let scrutinee =
                                      FStar_TypeChecker_Util.maybe_lift env
                                        scrutinee
                                        c1.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.eff_name
                                        c1.FStar_Syntax_Syntax.res_typ
                                       in
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____2809  ->
                                              match uu____2809 with
                                              | ((pat,wopt,br),uu____2825,lc,uu____2827)
                                                  ->
                                                  let uu____2834 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  (pat, wopt, _0_344)))
                                       in
                                    let e =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_match
                                            (scrutinee, branches)))
                                        (Some
                                           ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    (FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_ascribed
                                          (e3,
                                            ((FStar_Util.Inl
                                                (cres.FStar_Syntax_Syntax.res_typ)),
                                              None),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.eff_name)))))
                                      None e.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____2562 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  match uu____2562 with
                                  | true  -> mk_match e1
                                  | uu____2565 ->
                                      let e_match =
                                        mk_match
                                          (FStar_Syntax_Syntax.bv_to_name
                                             guard_x)
                                         in
                                      let lb =
                                        let _0_345 =
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
                                          FStar_Syntax_Syntax.lbeff = _0_345;
                                          FStar_Syntax_Syntax.lbdef = e1
                                        }  in
                                      let e =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_let
                                              (let _0_348 =
                                                 let _0_347 =
                                                   let _0_346 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       guard_x
                                                      in
                                                   [_0_346]  in
                                                 FStar_Syntax_Subst.close
                                                   _0_347 e_match
                                                  in
                                               ((false, [lb]), _0_348))))
                                          (Some
                                             ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env e
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ
                                   in
                                ((let uu____2586 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  match uu____2586 with
                                  | true  ->
                                      let _0_351 =
                                        FStar_Range.string_of_range
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      let _0_350 =
                                        let _0_349 =
                                          cres.FStar_Syntax_Syntax.comp ()
                                           in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Print.comp_to_string
                                          _0_349
                                         in
                                      FStar_Util.print2
                                        "(%s) comp type = %s\n" _0_351 _0_350
                                  | uu____2587 -> ());
                                 (let _0_352 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e, cres, _0_352))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2941;
                FStar_Syntax_Syntax.lbunivs = uu____2942;
                FStar_Syntax_Syntax.lbtyp = uu____2943;
                FStar_Syntax_Syntax.lbeff = uu____2944;
                FStar_Syntax_Syntax.lbdef = uu____2945;_}::[]),uu____2946)
           ->
           ((let uu____2610 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             match uu____2610 with
             | true  ->
                 let _0_353 = FStar_Syntax_Print.term_to_string top  in
                 FStar_Util.print1 "%s\n" _0_353
             | uu____2611 -> ());
            check_top_level_let env top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2612),uu____2613) ->
           check_inner_let env top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2975;
                FStar_Syntax_Syntax.lbunivs = uu____2976;
                FStar_Syntax_Syntax.lbtyp = uu____2977;
                FStar_Syntax_Syntax.lbeff = uu____2978;
                FStar_Syntax_Syntax.lbdef = uu____2979;_}::uu____2980),uu____2981)
           ->
           ((let uu____2645 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             match uu____2645 with
             | true  ->
                 let _0_354 = FStar_Syntax_Print.term_to_string top  in
                 FStar_Util.print1 "%s\n" _0_354
             | uu____2646 -> ());
            check_top_level_let_rec env top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____2647),uu____2648) ->
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
        let uu____2692 = FStar_TypeChecker_Util.maybe_instantiate env e t  in
        match uu____2692 with
        | (e,t,implicits) ->
            let tc =
              let uu____2705 = FStar_TypeChecker_Env.should_verify env  in
              match uu____2705 with
              | true  -> FStar_Util.Inl t
              | uu____2708 ->
                  FStar_Util.Inr
                    (let _0_355 = FStar_Syntax_Syntax.mk_Total t  in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       _0_355)
               in
            let is_data_ctor uu___78_2715 =
              match uu___78_2715 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____2718 -> false  in
            let uu____2720 =
              (is_data_ctor dc) &&
                (Prims.op_Negation
                   (FStar_TypeChecker_Env.is_datacon env
                      v.FStar_Syntax_Syntax.v))
               in
            (match uu____2720 with
             | true  ->
                 Prims.raise
                   (FStar_Errors.Error
                      (let _0_357 =
                         FStar_Util.format1
                           "Expected a data constructor; got %s"
                           (v.FStar_Syntax_Syntax.v).FStar_Ident.str
                          in
                       let _0_356 = FStar_TypeChecker_Env.get_range env  in
                       (_0_357, _0_356)))
             | uu____2731 -> value_check_expected_typ env e tc implicits)
         in
      let env = FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          failwith
            (let _0_358 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format1
               "Impossible: Violation of locally nameless convention: %s"
               _0_358)
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____2756 =
              (FStar_Syntax_Subst.compress t1).FStar_Syntax_Syntax.n  in
            match uu____2756 with
            | FStar_Syntax_Syntax.Tm_arrow uu____2757 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3155 ->
                let imp =
                  ("uvar in term", env, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___90_2785 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___95_3175.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___95_3175.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___95_3175.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env  in
          let uu____2813 =
            let uu____2820 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____2820 with
            | None  ->
                let uu____2828 = FStar_Syntax_Util.type_u ()  in
                (match uu____2828 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard)  in
          (match uu____2813 with
           | (t,uu____2849,g0) ->
               let uu____2857 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env t
                  in
               (match uu____2857 with
                | (e,uu____2868,g1) ->
                    let _0_361 =
                      let _0_359 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right _0_359
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let _0_360 = FStar_TypeChecker_Rel.conj_guard g0 g1  in
                    (e, _0_361, _0_360)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let t =
            match env.FStar_TypeChecker_Env.use_bv_sorts with
            | true  -> x.FStar_Syntax_Syntax.sort
            | uu____2882 -> FStar_TypeChecker_Env.lookup_bv env x  in
          let e =
            FStar_Syntax_Syntax.bv_to_name
              (let uu___91_2884 = x  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___91_2884.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___91_2884.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = t
               })
             in
          let uu____2885 = FStar_TypeChecker_Util.maybe_instantiate env e t
             in
          (match uu____2885 with
           | (e,t,implicits) ->
               let tc =
                 let uu____2898 = FStar_TypeChecker_Env.should_verify env  in
                 match uu____2898 with
                 | true  -> FStar_Util.Inl t
                 | uu____2901 ->
                     FStar_Util.Inr
                       (let _0_362 = FStar_Syntax_Syntax.mk_Total t  in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          _0_362)
                  in
               value_check_expected_typ env e tc implicits)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3320;
             FStar_Syntax_Syntax.pos = uu____3321;
             FStar_Syntax_Syntax.vars = uu____3322;_},us)
          ->
          let us = FStar_List.map (tc_universe env) us  in
          let uu____2915 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____2915 with
           | (us',t) ->
               ((match (FStar_List.length us) <> (FStar_List.length us') with
                 | true  ->
                     Prims.raise
                       (FStar_Errors.Error
                          (let _0_363 = FStar_TypeChecker_Env.get_range env
                              in
                           ("Unexpected number of universe instantiations",
                             _0_363)))
                 | uu____2932 ->
                     FStar_List.iter2
                       (fun u'  ->
                          fun u  ->
                            match u' with
                            | FStar_Syntax_Syntax.U_unif u'' ->
                                FStar_Unionfind.change u'' (Some u)
                            | uu____2939 -> failwith "Impossible") us' us);
                (let fv' =
                   let uu___92_2941 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___93_2942 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___98_3367.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___98_3367.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___97_3366.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___92_2941.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 let e =
                   let _0_364 =
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv'))
                       (Some (t.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst _0_364 us  in
                 check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name
                   fv'.FStar_Syntax_Syntax.fv_qual e t)))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2975 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____2975 with
           | (us,t) ->
               ((let uu____2988 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Range")
                    in
                 match uu____2988 with
                 | true  ->
                     let _0_369 =
                       FStar_Syntax_Print.lid_to_string
                         (FStar_Syntax_Syntax.lid_of_fv fv)
                        in
                     let _0_368 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let _0_367 =
                       FStar_Range.string_of_range
                         (FStar_Ident.range_of_lid
                            (FStar_Syntax_Syntax.lid_of_fv fv))
                        in
                     let _0_366 =
                       FStar_Range.string_of_use_range
                         (FStar_Ident.range_of_lid
                            (FStar_Syntax_Syntax.lid_of_fv fv))
                        in
                     let _0_365 = FStar_Syntax_Print.term_to_string t  in
                     FStar_Util.print5
                       "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s"
                       _0_369 _0_368 _0_367 _0_366 _0_365
                 | uu____2989 -> ());
                (let fv' =
                   let uu___94_2991 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___95_2992 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___100_3423.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___100_3423.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___99_3422.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___94_2991.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 let e =
                   let _0_370 =
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv'))
                       (Some (t.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst _0_370 us  in
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
          let uu____3049 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3049 with
           | (bs,c) ->
               let env0 = env  in
               let uu____3058 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____3058 with
                | (env,uu____3066) ->
                    let uu____3069 = tc_binders env bs  in
                    (match uu____3069 with
                     | (bs,env,g,us) ->
                         let uu____3081 = tc_comp env c  in
                         (match uu____3081 with
                          | (c,uc,f) ->
                              let e =
                                let uu___96_3094 =
                                  FStar_Syntax_Util.arrow bs c  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___101_3520.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___101_3520.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___96_3094.FStar_Syntax_Syntax.vars)
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
                                  let _0_371 =
                                    FStar_TypeChecker_Rel.close_guard bs f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g _0_371
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
          let uu____3149 =
            let _0_373 =
              let _0_372 = FStar_Syntax_Syntax.mk_binder x  in [_0_372]  in
            FStar_Syntax_Subst.open_term _0_373 phi  in
          (match uu____3149 with
           | (x,phi) ->
               let env0 = env  in
               let uu____3158 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____3158 with
                | (env,uu____3166) ->
                    let uu____3169 =
                      let _0_374 = FStar_List.hd x  in tc_binder env _0_374
                       in
                    (match uu____3169 with
                     | (x,env,f1,u) ->
                         ((let uu____3190 =
                             FStar_TypeChecker_Env.debug env
                               FStar_Options.High
                              in
                           match uu____3190 with
                           | true  ->
                               let _0_377 =
                                 FStar_Range.string_of_range
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let _0_376 =
                                 FStar_Syntax_Print.term_to_string phi  in
                               let _0_375 =
                                 FStar_Syntax_Print.bv_to_string
                                   (Prims.fst x)
                                  in
                               FStar_Util.print3
                                 "(%s) Checking refinement formula %s; binder is %s\n"
                                 _0_377 _0_376 _0_375
                           | uu____3191 -> ());
                          (let uu____3192 = FStar_Syntax_Util.type_u ()  in
                           match uu____3192 with
                           | (t_phi,uu____3199) ->
                               let uu____3200 =
                                 tc_check_tot_or_gtot_term env phi t_phi  in
                               (match uu____3200 with
                                | (phi,uu____3208,f2) ->
                                    let e =
                                      let uu___97_3213 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x) phi
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___102_3648.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___102_3648.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___97_3213.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let _0_378 =
                                        FStar_TypeChecker_Rel.close_guard 
                                          [x] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        _0_378
                                       in
                                    value_check_expected_typ env0 e
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3240) ->
          let bs = FStar_TypeChecker_Util.maybe_add_implicit_binders env bs
             in
          ((let uu____3265 =
              FStar_TypeChecker_Env.debug env FStar_Options.Low  in
            match uu____3265 with
            | true  ->
                let _0_379 =
                  FStar_Syntax_Print.term_to_string
                    (let uu___98_3266 = top  in
                     {
                       FStar_Syntax_Syntax.n =
                         (FStar_Syntax_Syntax.Tm_abs (bs, body, None));
                       FStar_Syntax_Syntax.tk =
                         (uu___98_3266.FStar_Syntax_Syntax.tk);
                       FStar_Syntax_Syntax.pos =
                         (uu___98_3266.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___98_3266.FStar_Syntax_Syntax.vars)
                     })
                   in
                FStar_Util.print1 "Abstraction is: %s\n" _0_379
            | uu____3284 -> ());
           (let uu____3285 = FStar_Syntax_Subst.open_term bs body  in
            match uu____3285 with | (bs,body) -> tc_abs env top bs body))
      | uu____3293 ->
          failwith
            (let _0_381 = FStar_Syntax_Print.term_to_string top  in
             let _0_380 = FStar_Syntax_Print.tag_of_term top  in
             FStar_Util.format2 "Unexpected value: %s (%s)" _0_381 _0_380)

and tc_constant :
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3739 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3740,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3746,Some uu____3747) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3755 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3759 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3760 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3761 ->
          FStar_TypeChecker_Common.t_range
      | uu____3762 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____3333) ->
          let uu____3340 = FStar_Syntax_Util.type_u ()  in
          (match uu____3340 with
           | (k,u) ->
               let uu____3348 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3348 with
                | (t,uu____3356,g) ->
                    let _0_382 = FStar_Syntax_Syntax.mk_Total' t (Some u)  in
                    (_0_382, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3359) ->
          let uu____3366 = FStar_Syntax_Util.type_u ()  in
          (match uu____3366 with
           | (k,u) ->
               let uu____3374 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3374 with
                | (t,uu____3382,g) ->
                    let _0_383 = FStar_Syntax_Syntax.mk_GTotal' t (Some u)
                       in
                    (_0_383, u, g)))
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
            (let _0_385 =
               let _0_384 =
                 FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ
                  in
               _0_384 :: (c.FStar_Syntax_Syntax.effect_args)  in
             FStar_Syntax_Syntax.mk_Tm_app head _0_385) None
              (c.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____3403 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____3403 with
           | (tc,uu____3411,f) ->
               let uu____3413 = FStar_Syntax_Util.head_and_args tc  in
               (match uu____3413 with
                | (head,args) ->
                    let comp_univs =
                      let uu____3443 =
                        (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                         in
                      match uu____3443 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3444,us) -> us
                      | uu____3450 -> []  in
                    let uu____3451 = FStar_Syntax_Util.head_and_args tc  in
                    (match uu____3451 with
                     | (uu____3464,args) ->
                         let uu____3480 =
                           let _0_387 = FStar_List.hd args  in
                           let _0_386 = FStar_List.tl args  in
                           (_0_387, _0_386)  in
                         (match uu____3480 with
                          | (res,args) ->
                              let uu____3532 =
                                let _0_388 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___83_4006  ->
                                          match uu___83_4006 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4012 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____3556 with
                                               | (env,uu____3563) ->
                                                   let uu____3566 =
                                                     tc_tot_or_gtot_term env
                                                       e
                                                      in
                                                   (match uu____3566 with
                                                    | (e,uu____3573,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e), g)))
                                          | f ->
                                              (f,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right _0_388 FStar_List.unzip
                                 in
                              (match uu____3532 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (Prims.fst res)
                                      in
                                   let c =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___99_3589 = c  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___104_4052.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (Prims.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___99_3589.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____3593 =
                                       FStar_TypeChecker_Util.effect_repr env
                                         c u
                                        in
                                     match uu____3593 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let _0_389 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c, u_c, _0_389))))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u =
        let u = FStar_Syntax_Subst.compress_univ u  in
        match u with
        | FStar_Syntax_Syntax.U_bvar uu____3603 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4070 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4070
        | FStar_Syntax_Syntax.U_max us ->
            FStar_Syntax_Syntax.U_max (FStar_List.map aux us)
        | FStar_Syntax_Syntax.U_name x -> u  in
      match env.FStar_TypeChecker_Env.lax_universes with
      | true  -> FStar_Syntax_Syntax.U_zero
      | uu____3609 ->
          (match u with
           | FStar_Syntax_Syntax.U_unknown  ->
               let _0_390 = FStar_Syntax_Util.type_u ()  in
               FStar_All.pipe_right _0_390 Prims.snd
           | uu____3612 -> aux u)

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
            Prims.raise
              (FStar_Errors.Error
                 (let _0_391 =
                    FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                      env msg t top
                     in
                  (_0_391, (top.FStar_Syntax_Syntax.pos))))
             in
          let check_binders env bs bs_expected =
            let rec aux uu____3686 bs bs_expected =
              match uu____3686 with
              | (env,out,g,subst) ->
                  (match (bs, bs_expected) with
                   | ([],[]) -> (env, (FStar_List.rev out), None, g, subst)
                   | ((hd,imp)::bs,(hd_expected,imp')::bs_expected) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             Prims.raise
                               (FStar_Errors.Error
                                  (let _0_394 =
                                     let _0_392 =
                                       FStar_Syntax_Print.bv_to_string hd  in
                                     FStar_Util.format1
                                       "Inconsistent implicit argument annotation on argument %s"
                                       _0_392
                                      in
                                   let _0_393 =
                                     FStar_Syntax_Syntax.range_of_bv hd  in
                                   (_0_394, _0_393)))
                         | uu____3783 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____3787 =
                           let uu____3790 =
                             (FStar_Syntax_Util.unmeta
                                hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              in
                           match uu____3790 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____3793 ->
                               ((let uu____3795 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.High
                                    in
                                 match uu____3795 with
                                 | true  ->
                                     let _0_395 =
                                       FStar_Syntax_Print.bv_to_string hd  in
                                     FStar_Util.print1 "Checking binder %s\n"
                                       _0_395
                                 | uu____3796 -> ());
                                (let uu____3797 =
                                   tc_tot_or_gtot_term env
                                     hd.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____3797 with
                                 | (t,uu____3804,g1) ->
                                     let g2 =
                                       let _0_397 =
                                         FStar_TypeChecker_Env.get_range env
                                          in
                                       let _0_396 =
                                         FStar_TypeChecker_Rel.teq env t
                                           expected_t
                                          in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4293
                                         "Type annotation on parameter incompatible with the expected type"
                                         _0_396
                                        in
                                     let g =
                                       let _0_398 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         _0_398
                                        in
                                     (t, g)))
                            in
                         match uu____3787 with
                         | (t,g) ->
                             let hd =
                               let uu___100_3823 = hd  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___105_4312.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___105_4312.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env = push_binding env b  in
                             let subst =
                               let _0_399 = FStar_Syntax_Syntax.bv_to_name hd
                                  in
                               maybe_extend_subst subst b_expected _0_399  in
                             aux (env, (b :: out), g, subst) bs bs_expected))
                   | (rest,[]) ->
                       (env2, (FStar_List.rev out),
                         (Some (FStar_Util.Inl rest)), g, subst1)
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
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____4423 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____3929 = tc_binders env bs  in
                  match uu____3929 with
                  | (bs,envbody,g,uu____3948) ->
                      let uu____3949 =
                        let uu____3954 =
                          (FStar_Syntax_Subst.compress body).FStar_Syntax_Syntax.n
                           in
                        match uu____3954 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,FStar_Util.Inr c,uu____3961) ->
                            let uu____3980 = tc_comp envbody c  in
                            (match uu____3980 with
                             | (c,uu____3989,g') ->
                                 let _0_400 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((Some c), body, _0_400))
                        | uu____3992 -> (None, body, g)  in
                      (match uu____3949 with
                       | (copt,body,g) ->
                           (None, bs, [], copt, envbody, body, g))))
            | Some t ->
                let t = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm t =
                  let uu____4042 =
                    (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
                  match uu____4042 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4071 -> failwith "Impossible");
                       (let uu____4075 = tc_binders env bs  in
                        match uu____4075 with
                        | (bs,envbody,g,uu____4095) ->
                            let uu____4096 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____4096 with
                             | (envbody,uu____4113) ->
                                 ((Some (t, true)), bs, [], None, envbody,
                                   body, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4124) ->
                      let uu____4129 =
                        as_function_typ norm b.FStar_Syntax_Syntax.sort  in
                      (match uu____4129 with
                       | (uu____4154,bs,bs',copt,env,body,g) ->
                           ((Some (t, false)), bs, bs', copt, env, body, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4190 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____4190 with
                       | (bs_expected,c_expected) ->
                           let check_actuals_against_formals env bs
                             bs_expected =
                             let rec handle_more uu____4251 c_expected =
                               match uu____4251 with
                               | (env,bs,more,guard,subst) ->
                                   (match more with
                                    | None  ->
                                        let _0_401 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected
                                           in
                                        (env, bs, guard, _0_401)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____4889 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            (FStar_Syntax_Util.arrow
                                               more_bs_expected c_expected)
                                           in
                                        let _0_402 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c
                                           in
                                        (env, bs, guard, _0_402)
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
                                                  let uu____4368 =
                                                    check_binders env more_bs
                                                      bs_expected
                                                     in
                                                  (match uu____4368 with
                                                   | (env,bs',more,guard',subst)
                                                       ->
                                                       let _0_404 =
                                                         let _0_403 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard guard'
                                                            in
                                                         (env,
                                                           (FStar_List.append
                                                              bs bs'), more,
                                                           _0_403, subst)
                                                          in
                                                       handle_more _0_404
                                                         c_expected)
                                              | uu____4403 ->
                                                  let _0_406 =
                                                    let _0_405 =
                                                      FStar_Syntax_Print.term_to_string
                                                        t
                                                       in
                                                    FStar_Util.format1
                                                      "More arguments than annotated type (%s)"
                                                      _0_405
                                                     in
                                                  fail _0_406 t)
                                         | uu____4411 ->
                                             fail
                                               "Function definition takes more arguments than expected from its annotated type"
                                               t))
                                in
                             let _0_407 = check_binders env bs bs_expected
                                in
                             handle_more _0_407 c_expected  in
                           let mk_letrec_env envbody bs c =
                             let letrecs = guard_letrecs envbody bs c  in
                             let envbody =
                               let uu___101_4441 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___106_5039.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___106_5039.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___106_5039.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___106_5039.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___106_5039.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___106_5039.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___106_5039.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___106_5039.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___106_5039.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___106_5039.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___106_5039.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___106_5039.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___106_5039.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___106_5039.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___106_5039.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___106_5039.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___106_5039.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___106_5039.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___106_5039.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___106_5039.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___106_5039.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___106_5039.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___101_4441.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5053  ->
                                     fun uu____5054  ->
                                       match (uu____5053, uu____5054) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5079 =
                                             let uu____5083 =
                                               let uu____5084 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env
                                                  in
                                               FStar_All.pipe_right _0_408
                                                 Prims.fst
                                                in
                                             tc_term _0_409 t  in
                                           (match uu____4481 with
                                            | (t,uu____4493,uu____4494) ->
                                                let env =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env l ([], t)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5104 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___102_4501
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___107_5105.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___107_5105.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t
                                                           })
                                                         in
                                                      _0_410 ::
                                                        letrec_binders
                                                  | uu____4502 ->
                                                      letrec_binders
                                                   in
                                                (env, lb))) (envbody, []))
                              in
                           let uu____4505 =
                             check_actuals_against_formals env bs bs_expected
                              in
                           (match uu____4505 with
                            | (envbody,bs,g,c) ->
                                let uu____4535 =
                                  let uu____4539 =
                                    FStar_TypeChecker_Env.should_verify env
                                     in
                                  match uu____4539 with
                                  | true  -> mk_letrec_env envbody bs c
                                  | uu____4543 -> (envbody, [])  in
                                (match uu____4535 with
                                 | (envbody,letrecs) ->
                                     let envbody =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((Some (t, false)), bs, letrecs,
                                       (Some c), envbody, body, g))))
                  | uu____4572 ->
                      (match Prims.op_Negation norm with
                       | true  ->
                           let _0_411 = unfold_whnf env t  in
                           as_function_typ true _0_411
                       | uu____4585 ->
                           let uu____4586 =
                             expected_function_typ env None body  in
                           (match uu____4586 with
                            | (uu____4610,bs,uu____4612,c_opt,envbody,body,g)
                                ->
                                ((Some (t, false)), bs, [], c_opt, envbody,
                                  body, g)))
                   in
                as_function_typ false t
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____4633 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____4633 with
          | (env,topt) ->
              ((let uu____4645 =
                  FStar_TypeChecker_Env.debug env FStar_Options.High  in
                match uu____4645 with
                | true  ->
                    let _0_412 =
                      match topt with
                      | None  -> "None"
                      | Some t -> FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                      _0_412
                      (match env.FStar_TypeChecker_Env.top_level with
                       | true  -> "true"
                       | uu____4647 -> "false")
                | uu____4648 -> ());
               (let uu____4649 = expected_function_typ env topt body  in
                match uu____4649 with
                | (tfun_opt,bs,letrec_binders,c_opt,envbody,body,g) ->
                    let uu____4679 =
                      tc_term
                        (let uu___103_4683 = envbody  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___108_5309.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___108_5309.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___108_5309.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___108_5309.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___108_5309.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___108_5309.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___108_5309.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___108_5309.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___108_5309.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___108_5309.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___108_5309.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___108_5309.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___108_5309.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___108_5309.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___108_5309.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___108_5309.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___108_5309.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___108_5309.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___108_5309.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___108_5309.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___108_5309.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___103_4683.FStar_TypeChecker_Env.qname_and_index)
                         }) body
                       in
                    (match uu____4679 with
                     | (body,cbody,guard_body) ->
                         let guard_body =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         ((let uu____4692 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Implicits")
                              in
                           match uu____4692 with
                           | true  ->
                               let _0_415 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length
                                      guard_body.FStar_TypeChecker_Env.implicits)
                                  in
                               let _0_414 =
                                 let _0_413 =
                                   cbody.FStar_Syntax_Syntax.comp ()  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Print.comp_to_string _0_413
                                  in
                               FStar_Util.print2
                                 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                                 _0_415 _0_414
                           | uu____4701 -> ());
                          (let uu____4702 =
                             let _0_417 =
                               let _0_416 = cbody.FStar_Syntax_Syntax.comp ()
                                  in
                               (body, _0_416)  in
                             check_expected_effect
                               (let uu___104_4706 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___109_5343.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___109_5343.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___109_5343.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___109_5343.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___109_5343.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___109_5343.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___109_5343.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___109_5343.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___109_5343.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___109_5343.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___109_5343.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___109_5343.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___109_5343.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___109_5343.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___109_5343.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___109_5343.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___109_5343.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___109_5343.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___109_5343.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___109_5343.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___109_5343.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___109_5343.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___104_4706.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt _0_417
                              in
                           match uu____4702 with
                           | (body,cbody,guard) ->
                               let guard =
                                 FStar_TypeChecker_Rel.conj_guard guard_body
                                   guard
                                  in
                               let guard =
                                 let uu____4717 =
                                   env.FStar_TypeChecker_Env.top_level ||
                                     (Prims.op_Negation
                                        (FStar_TypeChecker_Env.should_verify
                                           env))
                                    in
                                 match uu____4717 with
                                 | true  ->
                                     let _0_418 =
                                       FStar_TypeChecker_Rel.conj_guard g
                                         guard
                                        in
                                     FStar_TypeChecker_Rel.discharge_guard
                                       envbody _0_418
                                 | uu____4718 ->
                                     let guard =
                                       let _0_419 =
                                         FStar_TypeChecker_Rel.conj_guard g
                                           guard
                                          in
                                       FStar_TypeChecker_Rel.close_guard
                                         (FStar_List.append bs letrec_binders)
                                         _0_419
                                        in
                                     guard
                                  in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs cbody  in
                               let e =
                                 let _0_422 =
                                   Some
                                     (let _0_421 =
                                        FStar_All.pipe_right
                                          (FStar_Util.dflt cbody c_opt)
                                          FStar_Syntax_Util.lcomp_of_comp
                                         in
                                      FStar_All.pipe_right _0_421
                                        (fun _0_420  -> FStar_Util.Inl _0_420))
                                    in
                                 FStar_Syntax_Util.abs bs body _0_422  in
                               let uu____4739 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t = FStar_Syntax_Subst.compress t
                                        in
                                     (match t.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____4754 -> (e, t, guard)
                                      | uu____4762 ->
                                          let uu____4763 =
                                            match use_teq with
                                            | true  ->
                                                let _0_423 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env t tfun_computed
                                                   in
                                                (e, _0_423)
                                            | uu____4768 ->
                                                FStar_TypeChecker_Util.check_and_ascribe
                                                  env e tfun_computed t
                                             in
                                          (match uu____4763 with
                                           | (e,guard') ->
                                               let _0_424 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard guard'
                                                  in
                                               (e, t, _0_424)))
                                 | None  -> (e, tfun_computed, guard)  in
                               (match uu____4739 with
                                | (e,tfun,guard) ->
                                    let c =
                                      match env.FStar_TypeChecker_Env.top_level
                                      with
                                      | true  ->
                                          FStar_Syntax_Syntax.mk_Total tfun
                                      | uu____4785 ->
                                          FStar_TypeChecker_Util.return_value
                                            env tfun e
                                       in
                                    let uu____4786 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard
                                       in
                                    (match uu____4786 with
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
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = chead.FStar_Syntax_Syntax.res_typ  in
              (let uu____4822 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               match uu____4822 with
               | true  ->
                   let _0_426 =
                     FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos
                      in
                   let _0_425 = FStar_Syntax_Print.term_to_string thead  in
                   FStar_Util.print2 "(%s) Type of head is %s\n" _0_426
                     _0_425
               | uu____4823 -> ());
              (let monadic_application uu____4864 subst arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____5520 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head) env fvs
                         cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres =
                       let uu___105_4905 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___110_5561.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___110_5561.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___105_4905.FStar_Syntax_Syntax.comp)
                       }  in
                     let uu____4906 =
                       match bs with
                       | [] ->
                           let cres =
                             FStar_TypeChecker_Util.subst_lcomp subst cres
                              in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead guard  in
                           let refine_with_equality =
                             (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
                               &&
                               (FStar_All.pipe_right arg_comps_rev
                                  (FStar_Util.for_some
                                     (fun uu___84_5589  ->
                                        match uu___84_5589 with
                                        | (uu____5598,uu____5599,FStar_Util.Inl
                                           uu____5600) -> false
                                        | (uu____5611,uu____5612,FStar_Util.Inr
                                           c) ->
                                            Prims.op_Negation
                                              (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 c))))
                              in
                           let cres =
                             match refine_with_equality with
                             | true  ->
                                 let _0_427 =
                                   (FStar_Syntax_Syntax.mk_Tm_app head
                                      (FStar_List.rev arg_rets))
                                     (Some
                                        ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                     r
                                    in
                                 FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                   env _0_427 cres
                             | uu____4977 ->
                                 ((let uu____4979 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.Low
                                      in
                                   match uu____4979 with
                                   | true  ->
                                       let _0_430 =
                                         FStar_Syntax_Print.term_to_string
                                           head
                                          in
                                       let _0_429 =
                                         FStar_Syntax_Print.lcomp_to_string
                                           cres
                                          in
                                       let _0_428 =
                                         FStar_TypeChecker_Rel.guard_to_string
                                           env g
                                          in
                                       FStar_Util.print3
                                         "Not refining result: f=%s; cres=%s; guard=%s\n"
                                         _0_430 _0_429 _0_428
                                   | uu____4980 -> ());
                                  cres)
                              in
                           (cres, g)
                       | uu____4981 ->
                           let g =
                             let _0_431 =
                               FStar_TypeChecker_Rel.conj_guard ghead guard
                                in
                             FStar_All.pipe_right _0_431
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let _0_435 =
                             let _0_434 =
                               FStar_Syntax_Syntax.mk_Total
                                 (let _0_433 =
                                    let _0_432 =
                                      cres.FStar_Syntax_Syntax.comp ()  in
                                    FStar_Syntax_Util.arrow bs _0_432  in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.subst subst) _0_433)
                                in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp _0_434
                              in
                           (_0_435, g)
                        in
                     (match uu____4906 with
                      | (cres,guard) ->
                          ((let uu____4994 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            match uu____4994 with
                            | true  ->
                                let _0_436 =
                                  FStar_Syntax_Print.lcomp_to_string cres  in
                                FStar_Util.print1
                                  "\t Type of result cres is %s\n" _0_436
                            | uu____4995 -> ());
                           (let uu____4996 =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____5680  ->
                                     match uu____5680 with
                                     | ((e,q),x,c) ->
                                         (match c with
                                          | FStar_Util.Inl (eff_name,arg_typ)
                                              ->
                                              let _0_439 =
                                                let _0_438 =
                                                  let _0_437 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env e eff_name
                                                      out_c.FStar_Syntax_Syntax.eff_name
                                                      arg_typ
                                                     in
                                                  (_0_437, q)  in
                                                _0_438 :: args  in
                                              (_0_439, out_c, monadic)
                                          | FStar_Util.Inr c ->
                                              let monadic =
                                                monadic ||
                                                  (Prims.op_Negation
                                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                        c))
                                                 in
                                              let out_c =
                                                FStar_TypeChecker_Util.bind
                                                  e.FStar_Syntax_Syntax.pos
                                                  env None c (x, out_c)
                                                 in
                                              let e =
                                                FStar_TypeChecker_Util.maybe_monadic
                                                  env e
                                                  c.FStar_Syntax_Syntax.eff_name
                                                  c.FStar_Syntax_Syntax.res_typ
                                                 in
                                              let e =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env e
                                                  c.FStar_Syntax_Syntax.eff_name
                                                  out_c.FStar_Syntax_Syntax.eff_name
                                                  c.FStar_Syntax_Syntax.res_typ
                                                 in
                                              (((e, q) :: args), out_c,
                                                monadic))) ([], cres, false)
                                arg_comps_rev
                               in
                            match uu____4996 with
                            | (args,comp,monadic) ->
                                let comp =
                                  FStar_TypeChecker_Util.bind
                                    head.FStar_Syntax_Syntax.pos env None
                                    chead (None, comp)
                                   in
                                let app =
                                  (FStar_Syntax_Syntax.mk_Tm_app head args)
                                    (Some
                                       ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                    r
                                   in
                                let app =
                                  let uu____5155 =
                                    monadic ||
                                      (Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                            comp))
                                     in
                                  match uu____5155 with
                                  | true  ->
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env app
                                        comp.FStar_Syntax_Syntax.eff_name
                                        comp.FStar_Syntax_Syntax.res_typ
                                  | uu____5156 -> app  in
                                let uu____5157 =
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    None env app comp guard
                                   in
                                (match uu____5157 with
                                 | (comp,g) -> (app, comp, g)))))
                  in
               let rec tc_args head_info uu____5215 bs args =
                 match uu____5215 with
                 | (subst,outargs,arg_rets,g,fvs) ->
                     (match (bs, args) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____5310))::rest,
                         (uu____5312,None )::uu____5313) ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t = check_no_escape (Some head) env fvs t  in
                          let uu____5350 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head.FStar_Syntax_Syntax.pos env t
                             in
                          (match uu____5350 with
                           | (varg,uu____5361,implicits) ->
                               let subst = (FStar_Syntax_Syntax.NT (x, varg))
                                 :: subst  in
                               let arg =
                                 let _0_440 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, _0_440)  in
                               let _0_442 =
                                 let _0_441 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t))) :: outargs), (arg ::
                                   arg_rets), _0_441, fvs)
                                  in
                               tc_args head_info _0_442 rest args)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____6586 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x =
                              let uu___106_5471 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___111_6593.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___111_6593.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____5473 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             match uu____5473 with
                             | true  ->
                                 let _0_443 =
                                   FStar_Syntax_Print.term_to_string targ  in
                                 FStar_Util.print1
                                   "\tType of arg (after subst) = %s\n"
                                   _0_443
                             | uu____5474 -> ());
                            (let targ =
                               check_no_escape (Some head) env fvs targ  in
                             let env =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ
                                in
                             let env =
                               let uu___107_5478 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___112_6601.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___112_6601.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___112_6601.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___112_6601.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___112_6601.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___112_6601.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___112_6601.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___112_6601.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___112_6601.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___112_6601.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___112_6601.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___112_6601.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___112_6601.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___112_6601.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___112_6601.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___112_6601.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___112_6601.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___112_6601.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___112_6601.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___112_6601.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___112_6601.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___112_6601.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___107_5478.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             (let uu____5480 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.High
                                 in
                              match uu____5480 with
                              | true  ->
                                  let _0_446 =
                                    FStar_Syntax_Print.tag_of_term e  in
                                  let _0_445 =
                                    FStar_Syntax_Print.term_to_string e  in
                                  let _0_444 =
                                    FStar_Syntax_Print.term_to_string targ
                                     in
                                  FStar_Util.print3
                                    "Checking arg (%s) %s at type %s\n"
                                    _0_446 _0_445 _0_444
                              | uu____5481 -> ());
                             (let uu____5482 = tc_term env e  in
                              match uu____5482 with
                              | (e,c,g_e) ->
                                  let g =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e, aq)  in
                                  let uu____5498 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c
                                     in
                                  (match uu____5498 with
                                   | true  ->
                                       let subst =
                                         let _0_447 = FStar_List.hd bs  in
                                         maybe_extend_subst subst _0_447 e
                                          in
                                       tc_args head_info
                                         (subst2,
                                           ((arg, (Some x1),
                                              (FStar_Util.Inr c)) ::
                                           outargs), (arg :: arg_rets), g1,
                                           fvs) rest rest'
                                   | uu____5557 ->
                                       let uu____5558 =
                                         FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                           env c.FStar_Syntax_Syntax.eff_name
                                          in
                                       (match uu____5558 with
                                        | true  ->
                                            let subst =
                                              let _0_448 = FStar_List.hd bs
                                                 in
                                              maybe_extend_subst subst _0_448
                                                e
                                               in
                                            tc_args head_info
                                              (subst,
                                                ((arg, (Some x),
                                                   (FStar_Util.Inr c)) ::
                                                outargs), (arg :: arg_rets),
                                                g, fvs) rest rest'
                                        | uu____5607 ->
                                            let uu____5608 =
                                              FStar_Syntax_Syntax.is_null_binder
                                                (FStar_List.hd bs)
                                               in
                                            (match uu____5608 with
                                             | true  ->
                                                 let newx =
                                                   FStar_Syntax_Syntax.new_bv
                                                     (Some
                                                        (e.FStar_Syntax_Syntax.pos))
                                                     c.FStar_Syntax_Syntax.res_typ
                                                    in
                                                 let arg' =
                                                   let _0_449 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       newx
                                                      in
                                                   FStar_All.pipe_left
                                                     FStar_Syntax_Syntax.as_arg
                                                     _0_449
                                                    in
                                                 tc_args head_info
                                                   (subst,
                                                     ((arg, (Some newx),
                                                        (FStar_Util.Inr c))
                                                     :: outargs), (arg' ::
                                                     arg_rets), g, fvs) rest
                                                   rest'
                                             | uu____5653 ->
                                                 let _0_452 =
                                                   let _0_451 =
                                                     let _0_450 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         (FStar_Syntax_Syntax.bv_to_name
                                                            x)
                                                        in
                                                     _0_450 :: arg_rets  in
                                                   (subst,
                                                     ((arg, (Some x),
                                                        (FStar_Util.Inr c))
                                                     :: outargs), _0_451, g,
                                                     (x :: fvs))
                                                    in
                                                 tc_args head_info _0_452
                                                   rest rest')))))))
                      | (uu____5690,[]) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____5711) ->
                          let uu____5741 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs []
                             in
                          (match uu____5741 with
                           | (head,chead,ghead) ->
                               let rec aux norm tres =
                                 let tres =
                                   let _0_453 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right _0_453
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,cres') ->
                                     let uu____5779 =
                                       FStar_Syntax_Subst.open_comp bs cres'
                                        in
                                     (match uu____5779 with
                                      | (bs,cres') ->
                                          let head_info =
                                            (head, chead, ghead,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'))
                                             in
                                          ((let uu____5793 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            match uu____5793 with
                                            | true  ->
                                                let _0_454 =
                                                  FStar_Range.string_of_range
                                                    tres.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Util.print1
                                                  "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                  _0_454
                                            | uu____5794 -> ());
                                           tc_args head_info
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs args))
                                 | uu____5823 when Prims.op_Negation norm ->
                                     let _0_455 = unfold_whnf env tres  in
                                     aux true _0_455
                                 | uu____5824 ->
                                     Prims.raise
                                       (FStar_Errors.Error
                                          (let _0_459 =
                                             let _0_457 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env thead
                                                in
                                             let _0_456 =
                                               FStar_Util.string_of_int
                                                 n_args
                                                in
                                             FStar_Util.format2
                                               "Too many arguments to function of type %s; got %s arguments"
                                               _0_457 _0_456
                                              in
                                           let _0_458 =
                                             FStar_Syntax_Syntax.argpos arg
                                              in
                                           (_0_459, _0_458)))
                                  in
                               aux false chead.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app norm tf =
                 let uu____5843 =
                   (FStar_Syntax_Util.unrefine tf).FStar_Syntax_Syntax.n  in
                 match uu____5843 with
                 | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl ->
                           let uu____5917 = tc_term env e  in
                           (match uu____5917 with
                            | (e,c,g_e) ->
                                let uu____5930 = tc_args env tl  in
                                (match uu____5930 with
                                 | (args,comps,g_rest) ->
                                     let _0_460 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e, imp) :: args),
                                       (((e.FStar_Syntax_Syntax.pos), c) ::
                                       comps), _0_460)))
                        in
                     let uu____5962 = tc_args env args  in
                     (match uu____5962 with
                      | (args,comps,g_args) ->
                          let bs =
                            FStar_Syntax_Util.null_binders_of_tks
                              (FStar_All.pipe_right comps
                                 (FStar_List.map
                                    (fun uu____6000  ->
                                       match uu____6000 with
                                       | (uu____6008,c) ->
                                           ((c.FStar_Syntax_Syntax.res_typ),
                                             None))))
                             in
                          let ml_or_tot t r =
                            let uu____6024 = FStar_Options.ml_ish ()  in
                            match uu____6024 with
                            | true  -> FStar_Syntax_Util.ml_comp t r
                            | uu____6025 -> FStar_Syntax_Syntax.mk_Total t
                             in
                          let cres =
                            let _0_463 =
                              let _0_462 =
                                let _0_461 = FStar_Syntax_Util.type_u ()  in
                                FStar_All.pipe_right _0_461 Prims.fst  in
                              FStar_TypeChecker_Util.new_uvar env _0_462  in
                            ml_or_tot _0_463 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____6033 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            match uu____6033 with
                            | true  ->
                                let _0_466 =
                                  FStar_Syntax_Print.term_to_string head  in
                                let _0_465 =
                                  FStar_Syntax_Print.term_to_string tf  in
                                let _0_464 =
                                  FStar_Syntax_Print.term_to_string bs_cres
                                   in
                                FStar_Util.print3
                                  "Forcing the type of %s from %s to %s\n"
                                  _0_466 _0_465 _0_464
                            | uu____6034 -> ());
                           (let _0_467 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7221);
                           (let comp =
                              let uu____7223 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____7228  ->
                                   fun out  ->
                                     match uu____7228 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head.FStar_Syntax_Syntax.pos), chead) ::
                                comps) _0_468
                               in
                            let _0_470 =
                              (FStar_Syntax_Syntax.mk_Tm_app head args)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r
                               in
                            let _0_469 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (_0_470, comp, _0_469))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____6070 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____6070 with
                      | (bs,c) ->
                          let head_info =
                            (head, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c))
                             in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs args)
                 | uu____6113 ->
                     (match Prims.op_Negation norm with
                      | true  ->
                          let _0_471 = unfold_whnf env tf  in
                          check_function_app true _0_471
                      | uu____6119 ->
                          Prims.raise
                            (FStar_Errors.Error
                               (let _0_472 =
                                  FStar_TypeChecker_Err.expected_function_typ
                                    env tf
                                   in
                                (_0_472, (head.FStar_Syntax_Syntax.pos)))))
                  in
               let _0_474 =
                 let _0_473 = FStar_Syntax_Util.unrefine thead  in
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.WHNF] env _0_473
                  in
               check_function_app false _0_474)

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
                FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c  in
                  let uu____6170 =
                    FStar_List.fold_left2
                      (fun uu____7380  ->
                         fun uu____7381  ->
                           fun uu____7382  ->
                             match (uu____7380, uu____7381, uu____7382) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7426 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____6229 with
                                   | (e,c,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen
                                          in
                                       let g =
                                         let _0_475 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           _0_475 g
                                          in
                                       let ghost =
                                         ghost ||
                                           ((Prims.op_Negation
                                               (FStar_Syntax_Util.is_total_lcomp
                                                  c))
                                              &&
                                              (Prims.op_Negation
                                                 (FStar_TypeChecker_Util.is_pure_effect
                                                    env
                                                    c.FStar_Syntax_Syntax.eff_name)))
                                          in
                                       let _0_479 =
                                         let _0_477 =
                                           let _0_476 =
                                             FStar_Syntax_Syntax.as_arg e  in
                                           [_0_476]  in
                                         FStar_List.append seen _0_477  in
                                       let _0_478 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g
                                          in
                                       (_0_479, _0_478, ghost))))
                      ([], g_head, false) args bs
                     in
                  (match uu____6170 with
                   | (args,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head args)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r
                          in
                       let c =
                         match ghost with
                         | true  ->
                             let _0_480 = FStar_Syntax_Syntax.mk_GTotal res_t
                                in
                             FStar_All.pipe_right _0_480
                               FStar_Syntax_Util.lcomp_of_comp
                         | uu____6274 -> FStar_Syntax_Util.lcomp_of_comp c
                          in
                       let uu____6275 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c guard
                          in
                       (match uu____6275 with | (c,g) -> (e, c, g)))
              | uu____6287 ->
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
        let uu____6309 = FStar_Syntax_Subst.open_branch branch  in
        match uu____6309 with
        | (pattern,when_clause,branch_exp) ->
            let uu____6335 = branch  in
            (match uu____6335 with
             | (cpat,uu____6355,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7612 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0
                      in
                   match uu____6397 with
                   | (pat_bvs,exps,p) ->
                       ((let uu____6419 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         match uu____6419 with
                         | true  ->
                             let _0_482 = FStar_Syntax_Print.pat_to_string p0
                                in
                             let _0_481 = FStar_Syntax_Print.pat_to_string p
                                in
                             FStar_Util.print2
                               "Pattern %s elaborated to %s\n" _0_482 _0_481
                         | uu____6420 -> ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs
                            in
                         let uu____6422 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____6422 with
                         | (env1,uu____6435) ->
                             let env1 =
                               let uu___108_6439 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___113_7656.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___113_7656.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___113_7656.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___113_7656.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___113_7656.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___113_7656.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___113_7656.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___113_7656.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___113_7656.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___113_7656.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___113_7656.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___113_7656.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___113_7656.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___113_7656.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___113_7656.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___113_7656.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___113_7656.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___113_7656.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___113_7656.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___113_7656.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___113_7656.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___113_7656.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___108_6439.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             let uu____6441 =
                               let _0_498 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____7675 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High
                                             in
                                          match uu____6461 with
                                          | true  ->
                                              let _0_484 =
                                                FStar_Syntax_Print.term_to_string
                                                  e
                                                 in
                                              let _0_483 =
                                                FStar_Syntax_Print.term_to_string
                                                  pat_t
                                                 in
                                              FStar_Util.print2
                                                "Checking pattern expression %s against expected type %s\n"
                                                _0_484 _0_483
                                          | uu____6462 -> ());
                                         (let uu____6463 = tc_term env1 e  in
                                          match uu____6463 with
                                          | (e,lc,g) ->
                                              ((let uu____6473 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High
                                                   in
                                                match uu____6473 with
                                                | true  ->
                                                    let _0_486 =
                                                      FStar_TypeChecker_Normalize.term_to_string
                                                        env e
                                                       in
                                                    let _0_485 =
                                                      FStar_TypeChecker_Normalize.term_to_string
                                                        env
                                                        lc.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_Util.print2
                                                      "Pre-checked pattern expression %s at type %s\n"
                                                      _0_486 _0_485
                                                | uu____6474 -> ());
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
                                                let uu____6477 =
                                                  let _0_487 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___109_6478 = g
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___114_7697.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___114_7697.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___109_6478.FStar_TypeChecker_Env.implicits)
                                                       })
                                                     in
                                                  FStar_All.pipe_right _0_487
                                                    FStar_TypeChecker_Rel.resolve_implicits
                                                   in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e
                                                   in
                                                let uvars_to_string uvs =
                                                  let uu____7711 =
                                                    let uu____7713 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____7713
                                                      (FStar_List.map
                                                         (fun uu____7737  ->
                                                            match uu____7737
                                                            with
                                                            | (u,uu____7742)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u))
                                                     in
                                                  FStar_All.pipe_right _0_489
                                                    (FStar_String.concat ", ")
                                                   in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e'
                                                   in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t
                                                   in
                                                (let uu____6529 =
                                                   let _0_490 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2
                                                      in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation _0_490
                                                    in
                                                 match uu____6529 with
                                                 | true  ->
                                                     let unresolved =
                                                       let _0_491 =
                                                         FStar_Util.set_difference
                                                           uvs1 uvs2
                                                          in
                                                       FStar_All.pipe_right
                                                         _0_491
                                                         FStar_Util.set_elements
                                                        in
                                                     Prims.raise
                                                       (FStar_Errors.Error
                                                          (let _0_496 =
                                                             let _0_495 =
                                                               FStar_TypeChecker_Normalize.term_to_string
                                                                 env e'
                                                                in
                                                             let _0_494 =
                                                               FStar_TypeChecker_Normalize.term_to_string
                                                                 env
                                                                 expected_pat_t
                                                                in
                                                             let _0_493 =
                                                               let _0_492 =
                                                                 FStar_All.pipe_right
                                                                   unresolved
                                                                   (FStar_List.map
                                                                    (fun
                                                                    uu____6557
                                                                     ->
                                                                    match uu____7797
                                                                    with
                                                                    | 
                                                                    (u,uu____7805)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 _0_492
                                                                 (FStar_String.concat
                                                                    ", ")
                                                                in
                                                             FStar_Util.format3
                                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                               _0_495 _0_494
                                                               _0_493
                                                              in
                                                           (_0_496,
                                                             (p.FStar_Syntax_Syntax.p))))
                                                 | uu____6577 -> ());
                                                (let uu____6579 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High
                                                    in
                                                 match uu____6579 with
                                                 | true  ->
                                                     let _0_497 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e
                                                        in
                                                     FStar_Util.print1
                                                       "Done checking pattern expression %s\n"
                                                       _0_497
                                                 | uu____6580 -> ());
                                                (e, e'))))))
                                  in
                               FStar_All.pipe_right _0_498 FStar_List.unzip
                                in
                             (match uu____6441 with
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
                 let uu____6603 =
                   let _0_499 = FStar_TypeChecker_Env.push_bv env scrutinee
                      in
                   FStar_All.pipe_right _0_499
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____6603 with
                  | (scrutinee_env,uu____6619) ->
                      let uu____6622 = tc_pat true pat_t pattern  in
                      (match uu____6622 with
                       | (pattern,pat_bvs,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____7900 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____6665 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 (match uu____6665 with
                                  | true  ->
                                      Prims.raise
                                        (FStar_Errors.Error
                                           ("When clauses are not yet supported in --verify mode; they will be some day",
                                             (e.FStar_Syntax_Syntax.pos)))
                                  | uu____6672 ->
                                      let uu____6673 =
                                        let _0_500 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env
                                            FStar_TypeChecker_Common.t_bool
                                           in
                                        tc_term _0_500 e  in
                                      (match uu____6673 with
                                       | (e,c,g) -> ((Some e), g)))
                              in
                           (match uu____6650 with
                            | (when_clause,g_when) ->
                                let uu____6696 = tc_term pat_env branch_exp
                                   in
                                (match uu____6696 with
                                 | (branch_exp,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____7966 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_501  -> Some _0_501)
                                             _0_502
                                        in
                                     let uu____6728 =
                                       let eqs =
                                         let uu____6736 =
                                           Prims.op_Negation
                                             (FStar_TypeChecker_Env.should_verify
                                                env)
                                            in
                                         match uu____6736 with
                                         | true  -> None
                                         | uu____6742 ->
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
                                                       | uu____6762 ->
                                                           let clause =
                                                             FStar_Syntax_Util.mk_eq
                                                               pat_t pat_t
                                                               scrutinee_tm e
                                                              in
                                                           (match fopt with
                                                            | None  ->
                                                                Some clause
                                                            | Some f ->
                                                                let _0_504 =
                                                                  FStar_Syntax_Util.mk_disj
                                                                    clause f
                                                                   in
                                                                FStar_All.pipe_left
                                                                  (fun _0_503
                                                                     ->
                                                                    Some
                                                                    _0_503)
                                                                  _0_504))
                                                  None)
                                          in
                                       let uu____6791 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp c g_branch
                                          in
                                       match uu____6791 with
                                       | (c,g_branch) ->
                                           let uu____6801 =
                                             match (eqs, when_condition) with
                                             | uu____8021 when
                                                 let uu____8026 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8026
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
                                                 let _0_506 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c gf
                                                    in
                                                 let _0_505 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (_0_506, _0_505)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____8042 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     (FStar_Syntax_Util.mk_conj
                                                        f w)
                                                    in
                                                 let _0_509 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c g_fw
                                                    in
                                                 let _0_508 =
                                                   let _0_507 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     _0_507 g_when
                                                    in
                                                 (_0_509, _0_508)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let _0_510 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c g_w
                                                    in
                                                 (_0_510, g_when)
                                              in
                                           (match uu____6801 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs
                                                   in
                                                let _0_512 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs c_weak
                                                   in
                                                let _0_511 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    binders g_when_weak
                                                   in
                                                (_0_512, _0_511, g_branch))
                                        in
                                     (match uu____6728 with
                                      | (c,g_when,g_branch) ->
                                          let branch_guard =
                                            let uu____6898 =
                                              Prims.op_Negation
                                                (FStar_TypeChecker_Env.should_verify
                                                   env)
                                               in
                                            match uu____6898 with
                                            | true  ->
                                                FStar_Syntax_Util.t_true
                                            | uu____6899 ->
                                                let rec build_branch_guard
                                                  scrutinee_tm pat_exp =
                                                  let discriminate
                                                    scrutinee_tm f =
                                                    let uu____6931 =
                                                      let _0_514 =
                                                        FStar_List.length
                                                          (Prims.snd
                                                             (let _0_513 =
                                                                FStar_TypeChecker_Env.typ_of_datacon
                                                                  env
                                                                  f.FStar_Syntax_Syntax.v
                                                                 in
                                                              FStar_TypeChecker_Env.datacons_of_typ
                                                                env _0_513))
                                                         in
                                                      _0_514 >
                                                        (Prims.parse_int "1")
                                                       in
                                                    match uu____6931 with
                                                    | true  ->
                                                        let discriminator =
                                                          FStar_Syntax_Util.mk_discriminator
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        let uu____6944 =
                                                          FStar_TypeChecker_Env.try_lookup_lid
                                                            env discriminator
                                                           in
                                                        (match uu____6944
                                                         with
                                                         | None  -> []
                                                         | uu____6955 ->
                                                             let disc =
                                                               FStar_Syntax_Syntax.fvar
                                                                 discriminator
                                                                 FStar_Syntax_Syntax.Delta_equational
                                                                 None
                                                                in
                                                             let disc =
                                                               (let _0_516 =
                                                                  let _0_515
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm
                                                                     in
                                                                  [_0_515]
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Tm_app
                                                                  disc _0_516)
                                                                 None
                                                                 scrutinee_tm.FStar_Syntax_Syntax.pos
                                                                in
                                                             let _0_517 =
                                                               FStar_Syntax_Util.mk_eq
                                                                 FStar_Syntax_Util.t_bool
                                                                 FStar_Syntax_Util.t_bool
                                                                 disc
                                                                 FStar_Syntax_Const.exp_true_bool
                                                                in
                                                             [_0_517])
                                                    | uu____6971 -> []  in
                                                  let fail uu____6980 =
                                                    failwith
                                                      (let _0_520 =
                                                         FStar_Range.string_of_range
                                                           pat_exp.FStar_Syntax_Syntax.pos
                                                          in
                                                       let _0_519 =
                                                         FStar_Syntax_Print.term_to_string
                                                           pat_exp
                                                          in
                                                       let _0_518 =
                                                         FStar_Syntax_Print.tag_of_term
                                                           pat_exp
                                                          in
                                                       FStar_Util.format3
                                                         "tc_eqn: Impossible (%s) %s (%s)"
                                                         _0_520 _0_519 _0_518)
                                                     in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t,uu____7001) ->
                                                        head_constructor t
                                                    | uu____7007 -> fail ()
                                                     in
                                                  let pat_exp =
                                                    let _0_521 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp
                                                       in
                                                    FStar_All.pipe_right
                                                      _0_521
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
                                                      uu____7025 ->
                                                      let _0_526 =
                                                        (let _0_525 =
                                                           let _0_524 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               scrutinee_tm
                                                              in
                                                           let _0_523 =
                                                             let _0_522 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 pat_exp
                                                                in
                                                             [_0_522]  in
                                                           _0_524 :: _0_523
                                                            in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           FStar_Syntax_Util.teq
                                                           _0_525) None
                                                          scrutinee_tm.FStar_Syntax_Syntax.pos
                                                         in
                                                      [_0_526]
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                    _
                                                    |FStar_Syntax_Syntax.Tm_fvar
                                                    _ ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp
                                                         in
                                                      let uu____7043 =
                                                        Prims.op_Negation
                                                          (FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v)
                                                         in
                                                      (match uu____7043 with
                                                       | true  -> []
                                                       | uu____7049 ->
                                                           let _0_527 =
                                                             head_constructor
                                                               pat_exp
                                                              in
                                                           discriminate
                                                             scrutinee_tm
                                                             _0_527)
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head,args) ->
                                                      let f =
                                                        head_constructor head
                                                         in
                                                      let uu____7073 =
                                                        Prims.op_Negation
                                                          (FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v)
                                                         in
                                                      (match uu____7073 with
                                                       | true  -> []
                                                       | uu____7079 ->
                                                           let sub_term_guards
                                                             =
                                                             let _0_531 =
                                                               FStar_All.pipe_right
                                                                 args
                                                                 (FStar_List.mapi
                                                                    (
                                                                    fun i  ->
                                                                    fun
                                                                    uu____8279
                                                                     ->
                                                                    match uu____8279
                                                                    with
                                                                    | 
                                                                    (ei,uu____8286)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____7115
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____7115
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8307
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8316
                                                                    =
                                                                    let uu____8317
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None  in
                                                                    let _0_529
                                                                    =
                                                                    let uu____8323
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm
                                                                     in
                                                                    [_0_528]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8317
                                                                    uu____8322 in
                                                                    uu____8316
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                                in
                                                             FStar_All.pipe_right
                                                               _0_531
                                                               FStar_List.flatten
                                                              in
                                                           let _0_532 =
                                                             discriminate
                                                               scrutinee_tm f
                                                              in
                                                           FStar_List.append
                                                             _0_532
                                                             sub_term_guards)
                                                  | uu____7145 -> []  in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm pat =
                                                  let uu____7157 =
                                                    Prims.op_Negation
                                                      (FStar_TypeChecker_Env.should_verify
                                                         env)
                                                     in
                                                  match uu____7157 with
                                                  | true  ->
                                                      FStar_TypeChecker_Util.fvar_const
                                                        env
                                                        FStar_Syntax_Const.true_lid
                                                  | uu____7158 ->
                                                      let t =
                                                        let _0_533 =
                                                          build_branch_guard
                                                            scrutinee_tm pat
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.mk_conj_l
                                                          _0_533
                                                         in
                                                      let uu____7161 =
                                                        FStar_Syntax_Util.type_u
                                                          ()
                                                         in
                                                      (match uu____7161 with
                                                       | (k,uu____7165) ->
                                                           let uu____7166 =
                                                             tc_check_tot_or_gtot_term
                                                               scrutinee_env
                                                               t k
                                                              in
                                                           (match uu____7166
                                                            with
                                                            | (t,uu____7171,uu____7172)
                                                                -> t))
                                                   in
                                                let branch_guard =
                                                  let _0_534 =
                                                    FStar_All.pipe_right
                                                      norm_disj_exps
                                                      (FStar_List.map
                                                         (build_and_check_branch_guard
                                                            scrutinee_tm))
                                                     in
                                                  FStar_All.pipe_right _0_534
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
                                          ((let uu____7189 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            match uu____7189 with
                                            | true  ->
                                                let _0_535 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  _0_535
                                            | uu____7190 -> ());
                                           (let _0_536 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern, when_clause,
                                                  branch_exp)
                                               in
                                            (_0_536, branch_guard, c, guard)))))))))

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
          let uu____7208 = check_let_bound_def true env lb  in
          (match uu____7208 with
           | (e1,univ_vars,c1,g1,annotated) ->
               let uu____7222 =
                 match annotated &&
                         (Prims.op_Negation
                            env.FStar_TypeChecker_Env.generalize)
                 with
                 | true  -> (g1, e1, univ_vars, c1)
                 | uu____7231 ->
                     let g1 =
                       let _0_537 =
                         FStar_TypeChecker_Rel.solve_deferred_constraints env
                           g1
                          in
                       FStar_All.pipe_right _0_537
                         FStar_TypeChecker_Rel.resolve_implicits
                        in
                     let uu____7234 =
                       FStar_List.hd
                         (let _0_540 =
                            let _0_539 =
                              let _0_538 = c1.FStar_Syntax_Syntax.comp ()  in
                              ((lb.FStar_Syntax_Syntax.lbname), e1, _0_538)
                               in
                            [_0_539]  in
                          FStar_TypeChecker_Util.generalize env _0_540)
                        in
                     (match uu____7234 with
                      | (uu____7265,univs,e1,c1) ->
                          (g1, e1, univs,
                            (FStar_Syntax_Util.lcomp_of_comp c1)))
                  in
               (match uu____7222 with
                | (g1,e1,univ_vars,c1) ->
                    let uu____7276 =
                      let uu____7281 =
                        FStar_TypeChecker_Env.should_verify env  in
                      match uu____7281 with
                      | true  ->
                          let uu____7286 =
                            FStar_TypeChecker_Util.check_top_level env g1 c1
                             in
                          (match uu____7286 with
                           | (ok,c1) ->
                               (match ok with
                                | true  -> (e2, c1)
                                | uu____7301 ->
                                    ((let uu____7303 =
                                        FStar_Options.warn_top_level_effects
                                          ()
                                         in
                                      match uu____7303 with
                                      | true  ->
                                          let _0_541 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          FStar_Errors.warn _0_541
                                            FStar_TypeChecker_Err.top_level_effect
                                      | uu____7304 -> ());
                                     (let _0_542 =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_meta
                                              (e2,
                                                (FStar_Syntax_Syntax.Meta_desugared
                                                   FStar_Syntax_Syntax.Masked_effect))))
                                          None e2.FStar_Syntax_Syntax.pos
                                         in
                                      (_0_542, c1)))))
                      | uu____7321 ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                           (let c =
                              let _0_543 = c1.FStar_Syntax_Syntax.comp ()  in
                              FStar_All.pipe_right _0_543
                                (FStar_TypeChecker_Normalize.normalize_comp
                                   [FStar_TypeChecker_Normalize.Beta] env)
                               in
                            let e2 =
                              let uu____7329 =
                                FStar_Syntax_Util.is_pure_comp c  in
                              match uu____7329 with
                              | true  -> e2
                              | uu____7332 ->
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect))))
                                    None e2.FStar_Syntax_Syntax.pos
                               in
                            (e2, c)))
                       in
                    (match uu____7276 with
                     | (e2,c1) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_TypeChecker_Common.t_unit
                            in
                         (FStar_ST.write e2.FStar_Syntax_Syntax.tk
                            (Some
                               (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                          (let lb1 =
                             FStar_Syntax_Util.close_univs_and_mk_letbinding
                               None lb.FStar_Syntax_Syntax.lbname univ_vars
                               (FStar_Syntax_Util.comp_result c1)
                               (FStar_Syntax_Util.comp_effect_name c1) e1
                              in
                           let _0_544 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos
                              in
                           (_0_544, (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____7381 -> failwith "Impossible"

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
            let uu___110_7402 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___115_8622.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___115_8622.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___115_8622.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___115_8622.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___115_8622.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___115_8622.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___115_8622.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___115_8622.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___115_8622.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___115_8622.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___115_8622.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___115_8622.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___115_8622.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___115_8622.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___115_8622.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___115_8622.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___115_8622.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___115_8622.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___115_8622.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___115_8622.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___115_8622.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___115_8622.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___110_7402.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____7403 =
            let _0_546 =
              let _0_545 = FStar_TypeChecker_Env.clear_expected_typ env  in
              FStar_All.pipe_right _0_545 Prims.fst  in
            check_let_bound_def false _0_546 lb  in
          (match uu____7403 with
           | (e1,uu____7417,c1,g1,annotated) ->
               let x =
                 let uu___111_7422 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___116_8647.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___116_8647.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 }  in
               let uu____7423 =
                 let _0_548 =
                   let _0_547 = FStar_Syntax_Syntax.mk_binder x  in [_0_547]
                    in
                 FStar_Syntax_Subst.open_term _0_548 e2  in
               (match uu____7423 with
                | (xb,e2) ->
                    let xbinder = FStar_List.hd xb  in
                    let x = Prims.fst xbinder  in
                    let uu____7437 =
                      let _0_549 = FStar_TypeChecker_Env.push_bv env x  in
                      tc_term _0_549 e2  in
                    (match uu____7437 with
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
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 (let _0_550 = FStar_Syntax_Subst.close xb e2
                                     in
                                  ((false, [lb]), _0_550))))
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
                           let _0_553 =
                             let _0_552 = FStar_Syntax_Syntax.bv_to_name x
                                in
                             FStar_Syntax_Util.mk_eq
                               c1.FStar_Syntax_Syntax.res_typ
                               c1.FStar_Syntax_Syntax.res_typ _0_552 e1
                              in
                           FStar_All.pipe_left
                             (fun _0_551  ->
                                FStar_TypeChecker_Common.NonTrivial _0_551)
                             _0_553
                            in
                         let g2 =
                           let _0_555 =
                             let _0_554 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard _0_554 g2  in
                           FStar_TypeChecker_Rel.close_guard xb _0_555  in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g2
                            in
                         let uu____7475 =
                           FStar_Option.isSome
                             (FStar_TypeChecker_Env.expected_typ env)
                            in
                         (match uu____7475 with
                          | true  ->
                              let tt =
                                let _0_556 =
                                  FStar_TypeChecker_Env.expected_typ env  in
                                FStar_All.pipe_right _0_556 FStar_Option.get
                                 in
                              ((let uu____7482 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Exports")
                                   in
                                match uu____7482 with
                                | true  ->
                                    let _0_558 =
                                      FStar_Syntax_Print.term_to_string tt
                                       in
                                    let _0_557 =
                                      FStar_Syntax_Print.term_to_string
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    FStar_Util.print2
                                      "Got expected type from env %s\ncres.res_typ=%s\n"
                                      _0_558 _0_557
                                | uu____7483 -> ());
                               (e, cres, guard))
                          | uu____7484 ->
                              let t =
                                check_no_escape None env [x]
                                  cres.FStar_Syntax_Syntax.res_typ
                                 in
                              ((let uu____7487 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Exports")
                                   in
                                match uu____7487 with
                                | true  ->
                                    let _0_560 =
                                      FStar_Syntax_Print.term_to_string
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    let _0_559 =
                                      FStar_Syntax_Print.term_to_string t  in
                                    FStar_Util.print2
                                      "Checked %s has no escaping types; normalized to %s\n"
                                      _0_560 _0_559
                                | uu____7488 -> ());
                               (e,
                                 ((let uu___112_7489 = cres  in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___112_7489.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ = t;
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___112_7489.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (uu___112_7489.FStar_Syntax_Syntax.comp)
                                   })), guard))))))
      | uu____7490 -> failwith "Impossible"

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
          let uu____7511 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____7511 with
           | (lbs,e2) ->
               let uu____7522 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____7522 with
                | (env0,topt) ->
                    let uu____7533 = build_let_rec_env true env0 lbs  in
                    (match uu____7533 with
                     | (lbs,rec_env) ->
                         let uu____7544 = check_let_recs rec_env lbs  in
                         (match uu____7544 with
                          | (lbs,g_lbs) ->
                              let g_lbs =
                                let _0_561 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env g_lbs
                                   in
                                FStar_All.pipe_right _0_561
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____8810 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right _0_563
                                  (fun _0_562  -> Some _0_562)
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
                                            | uu____7573 ->
                                                FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                  all_lb_names
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  lb.FStar_Syntax_Syntax.lbunivs
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                  lb.FStar_Syntax_Syntax.lbeff
                                                  lb.FStar_Syntax_Syntax.lbdef))
                                | uu____7574 ->
                                    let ecs =
                                      let _0_565 =
                                        FStar_All.pipe_right lbs
                                          (FStar_List.map
                                             (fun lb  ->
                                                let _0_564 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    lb.FStar_Syntax_Syntax.lbtyp
                                                   in
                                                ((lb.FStar_Syntax_Syntax.lbname),
                                                  (lb.FStar_Syntax_Syntax.lbdef),
                                                  _0_564)))
                                         in
                                      FStar_TypeChecker_Util.generalize env
                                        _0_565
                                       in
                                    FStar_All.pipe_right ecs
                                      (FStar_List.map
                                         (fun uu____7617  ->
                                            match uu____7617 with
                                            | (x,uvs,e,c) ->
                                                FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                  all_lb_names x uvs
                                                  (FStar_Syntax_Util.comp_result
                                                     c)
                                                  (FStar_Syntax_Util.comp_effect_name
                                                     c) e))
                                 in
                              let cres =
                                let uu____8901 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp _0_566
                                 in
                              (FStar_ST.write e2.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____7648 =
                                  FStar_Syntax_Subst.close_let_rec lbs e2  in
                                match uu____7648 with
                                | (lbs,e2) ->
                                    let _0_568 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let _0_567 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env g_lbs
                                       in
                                    (_0_568, cres, _0_567)))))))
      | uu____7677 -> failwith "Impossible"

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
          let uu____7698 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____7698 with
           | (lbs,e2) ->
               let uu____7709 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____7709 with
                | (env0,topt) ->
                    let uu____7720 = build_let_rec_env false env0 lbs  in
                    (match uu____7720 with
                     | (lbs,rec_env) ->
                         let uu____7731 = check_let_recs rec_env lbs  in
                         (match uu____7731 with
                          | (lbs,g_lbs) ->
                              let uu____7742 =
                                FStar_All.pipe_right lbs
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___118_9015 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___118_9015.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___118_9015.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb =
                                            let uu___114_7755 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___119_9017.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___119_9017.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___119_9017.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___114_7755.FStar_Syntax_Syntax.lbdef)
                                            }  in
                                          let env =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb.FStar_Syntax_Syntax.lbtyp))
                                             in
                                          (env, lb)) env)
                                 in
                              (match uu____7742 with
                               | (env,lbs) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____7772 = tc_term env e2  in
                                   (match uu____7772 with
                                    | (e2,cres,g2) ->
                                        let guard =
                                          let uu____9045 =
                                            let uu____9046 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9046 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs g2
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
                                          let uu___115_7786 = cres  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___120_9050.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___120_9050.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___115_7786.FStar_Syntax_Syntax.comp)
                                          }  in
                                        let uu____7787 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs e2
                                           in
                                        (match uu____7787 with
                                         | (lbs,e2) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos
                                                in
                                             (match topt with
                                              | Some uu____9080 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres =
                                                    check_no_escape None env
                                                      bvs tres
                                                     in
                                                  let cres =
                                                    let uu___116_7821 = cres
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___121_9085.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___121_9085.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___116_7821.FStar_Syntax_Syntax.comp)
                                                    }  in
                                                  (e, cres, guard)))))))))
      | uu____7824 -> failwith "Impossible"

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
          let uu____7840 = FStar_Syntax_Util.arrow_formals_comp t  in
          match uu____7840 with
          | (uu____7846,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c)
                 in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)
           in
        let uu____7857 =
          FStar_List.fold_left
            (fun uu____9128  ->
               fun lb  ->
                 match uu____7864 with
                 | (lbs,env) ->
                     let uu____7876 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env
                         lb
                        in
                     (match uu____7876 with
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
                            | uu____7889 ->
                                let uu____7890 =
                                  let _0_570 =
                                    let _0_569 = FStar_Syntax_Util.type_u ()
                                       in
                                    FStar_All.pipe_left Prims.fst _0_569  in
                                  tc_check_tot_or_gtot_term
                                    (let uu___117_7894 = env0  in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___117_7894.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___117_7894.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___117_7894.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___117_7894.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___117_7894.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___117_7894.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___117_7894.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___117_7894.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___117_7894.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___117_7894.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___117_7894.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___117_7894.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___117_7894.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___117_7894.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         true;
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___117_7894.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___117_7894.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___117_7894.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___117_7894.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___117_7894.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___117_7894.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___117_7894.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         (uu___117_7894.FStar_TypeChecker_Env.use_bv_sorts);
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___117_7894.FStar_TypeChecker_Env.qname_and_index)
                                     }) t _0_570
                                   in
                                (match uu____7890 with
                                 | (t,uu____7898,g) ->
                                     let g =
                                       FStar_TypeChecker_Rel.resolve_implicits
                                         g
                                        in
                                     ((let _0_571 =
                                         FStar_TypeChecker_Rel.discharge_guard
                                           env g
                                          in
                                       FStar_All.pipe_left Prims.ignore
                                         _0_571);
                                      norm env0 t))
                             in
                          let env =
                            let uu____7903 =
                              (termination_check_enabled t) &&
                                (FStar_TypeChecker_Env.should_verify env)
                               in
                            match uu____7903 with
                            | true  ->
                                let uu___118_7904 = env  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___118_7904.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___118_7904.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___118_7904.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___118_7904.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___118_7904.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___118_7904.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___118_7904.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___118_7904.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___118_7904.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___118_7904.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___118_7904.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___118_7904.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (((lb.FStar_Syntax_Syntax.lbname), t) ::
                                    (env.FStar_TypeChecker_Env.letrecs));
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___118_7904.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___118_7904.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___118_7904.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___118_7904.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___118_7904.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___118_7904.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___118_7904.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___118_7904.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___118_7904.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___118_7904.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___118_7904.FStar_TypeChecker_Env.qname_and_index)
                                }
                            | uu____7911 ->
                                FStar_TypeChecker_Env.push_let_binding env
                                  lb.FStar_Syntax_Syntax.lbname ([], t)
                             in
                          let lb =
                            let uu___119_7914 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___124_9183.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___124_9183.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb :: lbs), env))) ([], env) lbs
           in
        match uu____7857 with | (lbs,env) -> ((FStar_List.rev lbs), env)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9197 =
        let uu____9202 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____9213 =
                    let uu____9217 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    tc_tot_or_gtot_term _0_572 lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____7947 with
                  | (e,c,g) ->
                      ((let uu____7957 =
                          Prims.op_Negation
                            (FStar_Syntax_Util.is_total_lcomp c)
                           in
                        match uu____7957 with
                        | true  ->
                            Prims.raise
                              (FStar_Errors.Error
                                 ("Expected let rec to be a Tot term; got effect GTot",
                                   (e.FStar_Syntax_Syntax.pos)))
                        | uu____7958 -> ());
                       (let lb =
                          FStar_Syntax_Util.mk_letbinding
                            lb.FStar_Syntax_Syntax.lbname
                            lb.FStar_Syntax_Syntax.lbunivs
                            lb.FStar_Syntax_Syntax.lbtyp
                            FStar_Syntax_Const.effect_Tot_lid e
                           in
                        (lb, g)))))
           in
        FStar_All.pipe_right _0_573 FStar_List.unzip  in
      match uu____7928 with
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
        let uu____7979 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____7979 with
        | (env1,uu____7989) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____7995 = check_lbtyp top_level env lb  in
            (match uu____7995 with
             | (topt,wf_annot,univ_vars,univ_opening,env1) ->
                 ((match (Prims.op_Negation top_level) && (univ_vars <> [])
                   with
                   | true  ->
                       Prims.raise
                         (FStar_Errors.Error
                            ("Inner let-bound definitions cannot be universe polymorphic",
                              (e1.FStar_Syntax_Syntax.pos)))
                   | uu____8018 -> ());
                  (let e1 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____8021 =
                     tc_maybe_toplevel_term
                       (let uu___120_8025 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___125_9300.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___125_9300.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___125_9300.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___125_9300.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___125_9300.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___125_9300.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___125_9300.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___125_9300.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___125_9300.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___125_9300.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___125_9300.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___125_9300.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___125_9300.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___125_9300.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___125_9300.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___125_9300.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___125_9300.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___125_9300.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___125_9300.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___125_9300.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___125_9300.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___125_9300.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___120_8025.FStar_TypeChecker_Env.qname_and_index)
                        }) e1
                      in
                   match uu____8021 with
                   | (e1,c1,g1) ->
                       let uu____8034 =
                         let _0_574 =
                           FStar_TypeChecker_Env.set_range env1
                             e1.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9315  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           _0_574 e1 c1 wf_annot
                          in
                       (match uu____8034 with
                        | (c1,guard_f) ->
                            let g1 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____8049 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              match uu____8049 with
                              | true  ->
                                  let _0_577 =
                                    FStar_Syntax_Print.lbname_to_string
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  let _0_576 =
                                    FStar_Syntax_Print.term_to_string
                                      c1.FStar_Syntax_Syntax.res_typ
                                     in
                                  let _0_575 =
                                    FStar_TypeChecker_Rel.guard_to_string env
                                      g1
                                     in
                                  FStar_Util.print3
                                    "checked top-level def %s, result type is %s, guard is %s\n"
                                    _0_577 _0_576 _0_575
                              | uu____8050 -> ());
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
            (if lb.FStar_Syntax_Syntax.lbunivs <> []
             then
               failwith
                 "Impossible: non-empty universe variables but the type is unknown"
             else ();
             (None, FStar_TypeChecker_Rel.trivial_guard, [], [], env))
        | uu____9354 ->
            let uu____9355 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____8076 with
             | (univ_opening,univ_vars) ->
                 let t = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 (match top_level &&
                          (Prims.op_Negation
                             env.FStar_TypeChecker_Env.generalize)
                  with
                  | true  ->
                      let _0_578 =
                        FStar_TypeChecker_Env.set_expected_typ env1 t  in
                      ((Some t), FStar_TypeChecker_Rel.trivial_guard,
                        univ_vars, univ_opening, _0_578)
                  | uu____8106 ->
                      let uu____8107 = FStar_Syntax_Util.type_u ()  in
                      (match uu____8107 with
                       | (k,uu____8118) ->
                           let uu____8119 =
                             tc_check_tot_or_gtot_term env1 t k  in
                           (match uu____8119 with
                            | (t,uu____8131,g) ->
                                ((let uu____8134 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Medium
                                     in
                                  match uu____8134 with
                                  | true  ->
                                      let _0_580 =
                                        FStar_Range.string_of_range
                                          (FStar_Syntax_Syntax.range_of_lbname
                                             lb.FStar_Syntax_Syntax.lbname)
                                         in
                                      let _0_579 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      FStar_Util.print2
                                        "(%s) Checked type annotation %s\n"
                                        _0_580 _0_579
                                  | uu____8135 -> ());
                                 (let t = norm env1 t  in
                                  let _0_581 =
                                    FStar_TypeChecker_Env.set_expected_typ
                                      env1 t
                                     in
                                  ((Some t), g, univ_vars, univ_opening,
                                    _0_581)))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9425  ->
      match uu____9425 with
      | (x,imp) ->
          let uu____8152 = FStar_Syntax_Util.type_u ()  in
          (match uu____8152 with
           | (tu,u) ->
               ((let uu____8164 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 match uu____8164 with
                 | true  ->
                     let _0_584 = FStar_Syntax_Print.bv_to_string x  in
                     let _0_583 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let _0_582 = FStar_Syntax_Print.term_to_string tu  in
                     FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                       _0_584 _0_583 _0_582
                 | uu____8165 -> ());
                (let uu____8166 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____8166 with
                 | (t,uu____8177,g) ->
                     let x =
                       ((let uu___121_8182 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___126_9469.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___126_9469.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____8184 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       match uu____8184 with
                       | true  ->
                           let _0_586 =
                             FStar_Syntax_Print.bv_to_string (Prims.fst x)
                              in
                           let _0_585 = FStar_Syntax_Print.term_to_string t
                              in
                           FStar_Util.print2 "Pushing binder %s at type %s\n"
                             _0_586 _0_585
                       | uu____8185 -> ());
                      (let _0_587 = push_binding env x  in (x, _0_587, g, u))))))

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
            let uu____8236 = tc_binder env b  in
            (match uu____8236 with
             | (b,env',g,u) ->
                 let uu____8259 = aux env' bs  in
                 (match uu____8259 with
                  | (bs,env',g',us) ->
                      let _0_589 =
                        let _0_588 = FStar_TypeChecker_Rel.close_guard [b] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g _0_588  in
                      ((b :: bs), env', _0_589, (u :: us))))
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
          (fun uu____8330  ->
             fun uu____8331  ->
               match (uu____8330, uu____8331) with
               | ((t,imp),(args,g)) ->
                   let uu____8368 = tc_term env t  in
                   (match uu____8368 with
                    | (t,uu____8378,g') ->
                        let _0_590 = FStar_TypeChecker_Rel.conj_guard g g'
                           in
                        (((t, imp) :: args), _0_590))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____8397  ->
             match uu____8397 with
             | (pats,g) ->
                 let uu____8411 = tc_args env p  in
                 (match uu____8411 with
                  | (args,g') ->
                      let _0_591 = FStar_TypeChecker_Rel.conj_guard g g'  in
                      ((args :: pats), _0_591))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____8426 = tc_maybe_toplevel_term env e  in
      match uu____8426 with
      | (e,c,g) ->
          let uu____8436 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          (match uu____8436 with
           | true  -> (e, c, g)
           | uu____8440 ->
               let g = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                  in
               let c = c.FStar_Syntax_Syntax.comp ()  in
               let c = norm_c env c  in
               let uu____8446 =
                 let uu____8449 =
                   FStar_TypeChecker_Util.is_pure_effect env
                     (FStar_Syntax_Util.comp_effect_name c)
                    in
                 match uu____8449 with
                 | true  ->
                     let _0_592 =
                       FStar_Syntax_Syntax.mk_Total
                         (FStar_Syntax_Util.comp_result c)
                        in
                     (_0_592, false)
                 | uu____8452 ->
                     let _0_593 =
                       FStar_Syntax_Syntax.mk_GTotal
                         (FStar_Syntax_Util.comp_result c)
                        in
                     (_0_593, true)
                  in
               (match uu____8446 with
                | (target_comp,allow_ghost) ->
                    let uu____8458 =
                      FStar_TypeChecker_Rel.sub_comp env c target_comp  in
                    (match uu____8458 with
                     | Some g' ->
                         let _0_594 = FStar_TypeChecker_Rel.conj_guard g g'
                            in
                         (e, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                           _0_594)
                     | uu____8464 ->
                         (match allow_ghost with
                          | true  ->
                              Prims.raise
                                (FStar_Errors.Error
                                   (let _0_595 =
                                      FStar_TypeChecker_Err.expected_ghost_expression
                                        e c
                                       in
                                    (_0_595, (e.FStar_Syntax_Syntax.pos))))
                          | uu____8472 ->
                              Prims.raise
                                (FStar_Errors.Error
                                   (let _0_596 =
                                      FStar_TypeChecker_Err.expected_pure_expression
                                        e c
                                       in
                                    (_0_596, (e.FStar_Syntax_Syntax.pos))))))))

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
      let uu____8485 = tc_tot_or_gtot_term env t  in
      match uu____8485 with
      | (t,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; (t, c))

let type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      (let uu____9812 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       match uu____8505 with
       | true  ->
           let _0_597 = FStar_Syntax_Print.term_to_string e  in
           FStar_Util.print1 "Checking term %s\n" _0_597
       | uu____8506 -> ());
      (let env =
         let uu___122_8508 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___127_9816.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___127_9816.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___127_9816.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___127_9816.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___127_9816.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___127_9816.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___127_9816.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___127_9816.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___127_9816.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___127_9816.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___127_9816.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___127_9816.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___127_9816.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___127_9816.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___127_9816.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___127_9816.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___127_9816.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___127_9816.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___127_9816.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___127_9816.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___122_8508.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____8509 =
         try tc_tot_or_gtot_term env e
         with
         | FStar_Errors.Error (msg,uu____8525) ->
             Prims.raise
               (FStar_Errors.Error
                  (let _0_598 = FStar_TypeChecker_Env.get_range env  in
                   ((Prims.strcat "Implicit argument: " msg), _0_598)))
          in
       match uu____8509 with
       | (t,c,g) ->
           let uu____8535 = FStar_Syntax_Util.is_total_lcomp c  in
           (match uu____8535 with
            | true  -> (t, (c.FStar_Syntax_Syntax.res_typ), g)
            | uu____8541 ->
                Prims.raise
                  (FStar_Errors.Error
                     (let _0_601 =
                        let _0_599 = FStar_Syntax_Print.term_to_string e  in
                        FStar_Util.format1
                          "Implicit argument: Expected a total term; got a ghost term: %s"
                          _0_599
                         in
                      let _0_600 = FStar_TypeChecker_Env.get_range env  in
                      (_0_601, _0_600)))))
  
let level_of_type_fail env e t =
  Prims.raise
    (FStar_Errors.Error
       (let _0_604 =
          let _0_602 = FStar_Syntax_Print.term_to_string e  in
          FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
            _0_602 t
           in
        let _0_603 = FStar_TypeChecker_Env.get_range env  in (_0_604, _0_603)))
  
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t =
          let uu____8578 =
            (FStar_Syntax_Util.unrefine t).FStar_Syntax_Syntax.n  in
          match uu____8578 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____8580 ->
              (match retry with
               | true  ->
                   let t =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env t
                      in
                   aux false t
               | uu____8582 ->
                   let uu____8583 = FStar_Syntax_Util.type_u ()  in
                   (match uu____8583 with
                    | (t_u,u) ->
                        let env =
                          let uu___125_8589 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___125_8589.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___125_8589.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___125_8589.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___125_8589.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___125_8589.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___125_8589.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___125_8589.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___125_8589.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___125_8589.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___125_8589.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___125_8589.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___125_8589.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___125_8589.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___125_8589.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___125_8589.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___125_8589.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___125_8589.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___125_8589.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___125_8589.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.type_of =
                              (uu___125_8589.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___125_8589.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___125_8589.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qname_and_index =
                              (uu___125_8589.FStar_TypeChecker_Env.qname_and_index)
                          }  in
                        let g = FStar_TypeChecker_Rel.teq env t t_u  in
                        ((match g.FStar_TypeChecker_Env.guard_f with
                          | FStar_TypeChecker_Common.NonTrivial f ->
                              let _0_605 =
                                FStar_Syntax_Print.term_to_string t  in
                              level_of_type_fail env e _0_605
                          | uu____8593 ->
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
      let uu____8602 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
         in
      match uu____8602 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____8609 ->
          let e = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____8620) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____9981,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____9996) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10003 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8667 with | (uu____8676,t) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10019,(FStar_Util.Inl t,uu____10021),uu____10022) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10058,(FStar_Util.Inr c,uu____10060),uu____10061) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10108;
             FStar_Syntax_Syntax.pos = uu____10109;
             FStar_Syntax_Syntax.vars = uu____10110;_},us)
          ->
          let uu____10116 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8739 with
           | (us',t) ->
               ((match (FStar_List.length us) <> (FStar_List.length us') with
                 | true  ->
                     Prims.raise
                       (FStar_Errors.Error
                          (let _0_606 = FStar_TypeChecker_Env.get_range env
                              in
                           ("Unexpected number of universe instantiations",
                             _0_606)))
                 | uu____8755 ->
                     FStar_List.iter2
                       (fun u'  ->
                          fun u  ->
                            match u' with
                            | FStar_Syntax_Syntax.U_unif u'' ->
                                FStar_Unionfind.change u'' (Some u)
                            | uu____8762 -> failwith "Impossible") us' us);
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10150 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10158) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____8788 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8788 with
           | (bs,c) ->
               let us =
                 FStar_List.map
                   (fun uu____8799  ->
                      match uu____8799 with
                      | (b,uu____8803) ->
                          let _0_607 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort _0_607)
                   bs
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c  in
                 let _0_608 = universe_of_aux env res  in
                 level_of_type env res _0_608  in
               let u_c =
                 let uu____8809 =
                   FStar_TypeChecker_Util.effect_repr env c u_res  in
                 match uu____8809 with
                 | None  -> u_res
                 | Some trepr ->
                     let _0_609 = universe_of_aux env trepr  in
                     level_of_type env trepr _0_609
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
                -> let _0_610 = universe_of_aux env hd  in (_0_610, args)
            | FStar_Syntax_Syntax.Tm_match (uu____8904,hd::uu____8906) ->
                let uu____8953 = FStar_Syntax_Subst.open_branch hd  in
                (match uu____8953 with
                 | (uu____8963,uu____8964,hd) ->
                     let uu____8980 = FStar_Syntax_Util.head_and_args hd  in
                     (match uu____8980 with
                      | (hd,args) -> type_of_head retry hd args))
            | uu____9015 when retry ->
                let e =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____9017 = FStar_Syntax_Util.head_and_args e  in
                (match uu____9017 with
                 | (hd,args) -> type_of_head false hd args)
            | uu____9052 ->
                let uu____9053 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                (match uu____9053 with
                 | (env,uu____9067) ->
                     let env =
                       let uu___126_9071 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___131_10464.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___131_10464.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___131_10464.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___131_10464.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___131_10464.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___131_10464.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___131_10464.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___131_10464.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___131_10464.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___131_10464.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___131_10464.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___131_10464.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___131_10464.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___131_10464.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___131_10464.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___131_10464.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___131_10464.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___131_10464.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___131_10464.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___131_10464.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___126_9071.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     ((let uu____9073 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "UniverseOf")
                          in
                       match uu____9073 with
                       | true  ->
                           let _0_612 =
                             FStar_Range.string_of_range
                               (FStar_TypeChecker_Env.get_range env)
                              in
                           let _0_611 = FStar_Syntax_Print.term_to_string hd
                              in
                           FStar_Util.print2 "%s: About to type-check %s\n"
                             _0_612 _0_611
                       | uu____9074 -> ());
                      (let uu____9075 = tc_term env hd  in
                       match uu____9075 with
                       | (uu____9088,{
                                       FStar_Syntax_Syntax.eff_name =
                                         uu____9089;
                                       FStar_Syntax_Syntax.res_typ = t;
                                       FStar_Syntax_Syntax.cflags =
                                         uu____9091;
                                       FStar_Syntax_Syntax.comp = uu____9092;_},g)
                           ->
                           ((let uu____10498 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env g
                                in
                             FStar_All.pipe_right _0_613 Prims.ignore);
                            (t, args)))))
             in
          let uu____9109 = type_of_head true hd args  in
          (match uu____9109 with
           | (t,args) ->
               let t =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____9138 = FStar_Syntax_Util.arrow_formals_comp t  in
               (match uu____9138 with
                | (bs,res) ->
                    let res = FStar_Syntax_Util.comp_result res  in
                    (match (FStar_List.length bs) = (FStar_List.length args)
                     with
                     | true  ->
                         let subst = FStar_Syntax_Util.subst_of_list bs args
                            in
                         FStar_Syntax_Subst.subst subst res
                     | uu____9170 ->
                         let _0_614 = FStar_Syntax_Print.term_to_string res
                            in
                         level_of_type_fail env e _0_614)))
      | FStar_Syntax_Syntax.Tm_match (uu____9173,hd::uu____9175) ->
          let uu____9222 = FStar_Syntax_Subst.open_branch hd  in
          (match uu____9222 with
           | (uu____9225,uu____9226,hd) -> universe_of_aux env hd)
      | FStar_Syntax_Syntax.Tm_match (uu____9242,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let _0_615 = universe_of_aux env e  in level_of_type env e _0_615
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____9288 = tc_binders env tps  in
      match uu____9288 with
      | (tps,env,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (tps, env, us))
  