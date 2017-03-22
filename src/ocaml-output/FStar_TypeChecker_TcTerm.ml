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
             if tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos
                 tl.FStar_Syntax_Syntax.pos
              in
           (let _0_255 =
              let _0_254 = FStar_Syntax_Syntax.as_arg v  in
              let _0_253 =
                let _0_252 = FStar_Syntax_Syntax.as_arg tl  in [_0_252]  in
              _0_254 :: _0_253  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _0_255)
             (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r) vs
      FStar_Syntax_Util.lex_top
  
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.bool =
  fun uu___78_41  ->
    match uu___78_41 with
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
                let t = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t  in
                let uu____100 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____100 with
                 | None  -> t
                 | Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t
                     else
                       (let fail uu____108 =
                          let msg =
                            match head_opt with
                            | None  ->
                                let _0_256 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  _0_256
                            | Some head ->
                                let _0_258 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let _0_257 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  _0_258 _0_257
                             in
                          Prims.raise
                            (FStar_Errors.Error
                               (let _0_259 =
                                  FStar_TypeChecker_Env.get_range env  in
                                (msg, _0_259)))
                           in
                        let s =
                          let _0_261 =
                            let _0_260 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left Prims.fst _0_260  in
                          FStar_TypeChecker_Util.new_uvar env _0_261  in
                        let uu____114 = FStar_TypeChecker_Rel.try_teq env t s
                           in
                        match uu____114 with
                        | Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____118 -> fail ()))
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
        if uu____149
        then s
        else (FStar_Syntax_Syntax.NT ((Prims.fst b), v)) :: s
  
let set_lcomp_result :
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___85_163 = lc  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___85_163.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___85_163.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____164  ->
             let _0_262 = lc.FStar_Syntax_Syntax.comp ()  in
             FStar_Syntax_Util.set_result_typ _0_262 t)
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
                if uu____214
                then
                  let t =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c)
                     in
                  let uu____216 =
                    (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
                  (match uu____216 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____218 -> false
                   | uu____219 -> true)
                else false
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
                   if uu____224
                   then FStar_Syntax_Syntax.mk_Total t
                   else FStar_TypeChecker_Util.return_value env t e)
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____232 =
            let uu____236 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____236 with
            | None  -> let _0_263 = memo_tk e t  in (_0_263, lc, guard)
            | Some t' ->
                ((let uu____243 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High  in
                  if uu____243
                  then
                    let _0_265 = FStar_Syntax_Print.term_to_string t  in
                    let _0_264 = FStar_Syntax_Print.term_to_string t'  in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" _0_265
                      _0_264
                  else ());
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
                             if uu____265
                             then
                               let _0_269 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let _0_268 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let _0_267 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let _0_266 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 _0_269 _0_268 _0_267 _0_266
                             else ());
                            (let msg =
                               let uu____271 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               if uu____271
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_270  -> Some _0_270)
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
                                 let _0_271 = memo_tk e t'  in
                                 (_0_271, (set_lcomp_result lc t'), g))))))
             in
          match uu____232 with
          | (e,lc,g) ->
              ((let uu____301 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                if uu____301
                then
                  let _0_272 = FStar_Syntax_Print.lcomp_to_string lc  in
                  FStar_Util.print1 "Return comp type is %s\n" _0_272
                else ());
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
      fun uu____346  ->
        match uu____346 with
        | (e,c) ->
            let expected_c_opt =
              match copt with
              | Some uu____361 -> copt
              | None  ->
                  let uu____362 =
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
                  if uu____362
                  then
                    Some
                      (FStar_Syntax_Util.ml_comp
                         (FStar_Syntax_Util.comp_result c)
                         e.FStar_Syntax_Syntax.pos)
                  else
                    (let uu____365 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____365
                     then None
                     else
                       (let uu____368 = FStar_Syntax_Util.is_pure_comp c  in
                        if uu____368
                        then
                          Some
                            (FStar_Syntax_Syntax.mk_Total
                               (FStar_Syntax_Util.comp_result c))
                        else
                          (let uu____371 =
                             FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                           if uu____371
                           then
                             Some
                               (FStar_Syntax_Syntax.mk_GTotal
                                  (FStar_Syntax_Util.comp_result c))
                           else None)))
               in
            (match expected_c_opt with
             | None  ->
                 let _0_273 = norm_c env c  in
                 (e, _0_273, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____379 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                   if uu____379
                   then
                     let _0_276 = FStar_Syntax_Print.term_to_string e  in
                     let _0_275 = FStar_Syntax_Print.comp_to_string c  in
                     let _0_274 =
                       FStar_Syntax_Print.comp_to_string expected_c  in
                     FStar_Util.print3
                       "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                       _0_276 _0_275 _0_274
                   else ());
                  (let c = norm_c env c  in
                   (let uu____383 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                    if uu____383
                    then
                      let _0_279 = FStar_Syntax_Print.term_to_string e  in
                      let _0_278 = FStar_Syntax_Print.comp_to_string c  in
                      let _0_277 =
                        FStar_Syntax_Print.comp_to_string expected_c  in
                      FStar_Util.print3
                        "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                        _0_279 _0_278 _0_277
                    else ());
                   (let uu____385 =
                      FStar_TypeChecker_Util.check_comp env e c expected_c
                       in
                    match uu____385 with
                    | (e,uu____393,g) ->
                        let g =
                          let _0_280 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_TypeChecker_Util.label_guard _0_280
                            "could not prove post-condition" g
                           in
                        ((let uu____397 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low
                             in
                          if uu____397
                          then
                            let _0_282 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos
                               in
                            let _0_281 =
                              FStar_TypeChecker_Rel.guard_to_string env g  in
                            FStar_Util.print2
                              "(%s) DONE check_expected_effect; guard is: %s\n"
                              _0_282 _0_281
                          else ());
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
                (let _0_284 =
                   FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                     env f
                    in
                 let _0_283 = FStar_TypeChecker_Env.get_range env  in
                 (_0_284, _0_283))))
  
let print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____437 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____437 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let _0_285 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" _0_285
  
let check_smt_pat env t bs c =
  let uu____474 = FStar_Syntax_Util.is_smt_lemma t  in
  if uu____474
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____475;
          FStar_Syntax_Syntax.effect_name = uu____476;
          FStar_Syntax_Syntax.result_typ = uu____477;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____481)::[];
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
             let _0_287 =
               let _0_286 = FStar_Syntax_Print.bv_to_string x  in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" _0_286
                in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos _0_287)
    | uu____539 -> failwith "Impossible"
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
        let uu____560 =
          Prims.op_Negation (FStar_TypeChecker_Env.should_verify env)  in
        if uu____560
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env  in
               let env =
                 let uu___86_578 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___86_578.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___86_578.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___86_578.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___86_578.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___86_578.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___86_578.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___86_578.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___86_578.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___86_578.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___86_578.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___86_578.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___86_578.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___86_578.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___86_578.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___86_578.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___86_578.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___86_578.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___86_578.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___86_578.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___86_578.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___86_578.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___86_578.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___86_578.FStar_TypeChecker_Env.qname_and_index)
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
                                 let _0_288 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort
                                    in
                                 unfold_whnf env _0_288  in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type _
                                  |FStar_Syntax_Syntax.Tm_arrow _ -> []
                                | uu____611 ->
                                    let _0_289 =
                                      FStar_Syntax_Syntax.bv_to_name b  in
                                    [_0_289])))
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
                        (fun uu___79_650  ->
                           match uu___79_650 with
                           | FStar_Syntax_Syntax.DECREASES uu____651 -> true
                           | uu____654 -> false))
                    in
                 match uu____646 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____658 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions  in
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
                                        if uu____723
                                        then
                                          let _0_291 =
                                            let _0_290 =
                                              Some
                                                (FStar_Syntax_Syntax.range_of_bv
                                                   x)
                                               in
                                            FStar_Syntax_Syntax.new_bv _0_290
                                              x.FStar_Syntax_Syntax.sort
                                             in
                                          (_0_291, imp)
                                        else (x, imp)))
                             in
                          let uu____727 =
                            FStar_Syntax_Subst.open_comp formals c  in
                          (match uu____727 with
                           | (formals,c) ->
                               let dec = decreases_clause formals c  in
                               let precedes =
                                 (let _0_295 =
                                    let _0_294 =
                                      FStar_Syntax_Syntax.as_arg dec  in
                                    let _0_293 =
                                      let _0_292 =
                                        FStar_Syntax_Syntax.as_arg
                                          previous_dec
                                         in
                                      [_0_292]  in
                                    _0_294 :: _0_293  in
                                  FStar_Syntax_Syntax.mk_Tm_app precedes
                                    _0_295) None r
                                  in
                               let uu____744 = FStar_Util.prefix formals  in
                               (match uu____744 with
                                | (bs,(last,imp)) ->
                                    let last =
                                      let uu___87_770 = last  in
                                      let _0_296 =
                                        FStar_Syntax_Util.refine last
                                          precedes
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___87_770.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___87_770.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = _0_296
                                      }  in
                                    let refined_formals =
                                      FStar_List.append bs [(last, imp)]  in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c
                                       in
                                    ((let uu____785 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Low
                                         in
                                      if uu____785
                                      then
                                        let _0_299 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l
                                           in
                                        let _0_298 =
                                          FStar_Syntax_Print.term_to_string t
                                           in
                                        let _0_297 =
                                          FStar_Syntax_Print.term_to_string
                                            t'
                                           in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          _0_299 _0_298 _0_297
                                      else ());
                                     (l, t'))))
                      | uu____789 ->
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
        (let uu___88_1053 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___88_1053.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___88_1053.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___88_1053.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___88_1053.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___88_1053.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___88_1053.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___88_1053.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___88_1053.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___88_1053.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___88_1053.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___88_1053.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___88_1053.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___88_1053.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___88_1053.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___88_1053.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___88_1053.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___88_1053.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___88_1053.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___88_1053.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___88_1053.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___88_1053.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___88_1053.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___88_1053.FStar_TypeChecker_Env.qname_and_index)
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
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      (let uu____1062 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       if uu____1062
       then
         let _0_302 =
           let _0_300 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range _0_300  in
         let _0_301 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" _0_302 _0_301
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1068 -> failwith "Impossible"
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
           let uu____1107 = tc_tot_or_gtot_term env e  in
           (match uu____1107 with
            | (e,c,g) ->
                let g =
                  let uu___89_1118 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___89_1118.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___89_1118.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___89_1118.FStar_TypeChecker_Env.implicits)
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
                            let uu___90_1192 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___90_1192.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___90_1192.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___90_1192.FStar_TypeChecker_Env.implicits)
                            }  in
                          let _0_304 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e,
                                    (FStar_Syntax_Syntax.Meta_pattern pats))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let _0_303 = FStar_TypeChecker_Rel.conj_guard g g'
                             in
                          (_0_304, c, _0_303))))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1212 =
             (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n  in
           (match uu____1212 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1216,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1218;
                               FStar_Syntax_Syntax.lbtyp = uu____1219;
                               FStar_Syntax_Syntax.lbeff = uu____1220;
                               FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
                ->
                let uu____1238 =
                  let _0_305 =
                    FStar_TypeChecker_Env.set_expected_typ env
                      FStar_TypeChecker_Common.t_unit
                     in
                  tc_term _0_305 e1  in
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
                                  (let _0_308 =
                                     let _0_307 =
                                       let _0_306 =
                                         FStar_Syntax_Syntax.mk_lb
                                           (x, [],
                                             (c1.FStar_Syntax_Syntax.eff_name),
                                             FStar_TypeChecker_Common.t_unit,
                                             e1)
                                          in
                                       [_0_306]  in
                                     (false, _0_307)  in
                                   (_0_308, e2))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              e.FStar_Syntax_Syntax.pos
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
                          let _0_309 = FStar_TypeChecker_Rel.conj_guard g1 g2
                             in
                          (e, c, _0_309)))
            | uu____1295 ->
                let uu____1296 = tc_term env e  in
                (match uu____1296 with
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
           (e,FStar_Syntax_Syntax.Meta_monadic uu____1320) -> tc_term env e
       | FStar_Syntax_Syntax.Tm_meta (e,m) ->
           let uu____1335 = tc_term env e  in
           (match uu____1335 with
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
           (e,FStar_Util.Inr expected_c,uu____1360) ->
           let uu____1379 = FStar_TypeChecker_Env.clear_expected_typ env  in
           (match uu____1379 with
            | (env0,uu____1387) ->
                let uu____1390 = tc_comp env0 expected_c  in
                (match uu____1390 with
                 | (expected_c,uu____1398,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c  in
                     let uu____1403 =
                       let _0_310 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term _0_310 e  in
                     (match uu____1403 with
                      | (e,c',g') ->
                          let uu____1413 =
                            let _0_312 =
                              let _0_311 = c'.FStar_Syntax_Syntax.comp ()  in
                              (e, _0_311)  in
                            check_expected_effect env0 (Some expected_c)
                              _0_312
                             in
                          (match uu____1413 with
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
                                 let _0_313 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g _0_313
                                  in
                               let uu____1449 =
                                 comp_check_expected_typ env e lc  in
                               (match uu____1449 with
                                | (e,c,f2) ->
                                    let _0_314 =
                                      FStar_TypeChecker_Rel.conj_guard f f2
                                       in
                                    (e, c, _0_314))))))
       | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t,uu____1461) ->
           let uu____1480 = FStar_Syntax_Util.type_u ()  in
           (match uu____1480 with
            | (k,u) ->
                let uu____1488 = tc_check_tot_or_gtot_term env t k  in
                (match uu____1488 with
                 | (t,uu____1496,f) ->
                     let uu____1498 =
                       let _0_315 =
                         FStar_TypeChecker_Env.set_expected_typ env t  in
                       tc_term _0_315 e  in
                     (match uu____1498 with
                      | (e,c,g) ->
                          let uu____1508 =
                            let _0_316 =
                              FStar_TypeChecker_Env.set_range env
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1513  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              _0_316 e c f
                             in
                          (match uu____1508 with
                           | (c,f) ->
                               let uu____1519 =
                                 let _0_317 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e, (FStar_Util.Inl t),
                                           (Some
                                              (c.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env _0_317 c  in
                               (match uu____1519 with
                                | (e,c,f2) ->
                                    let _0_319 =
                                      let _0_318 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f
                                        _0_318
                                       in
                                    (e, c, _0_319))))))
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
           let uu____1624 = FStar_Syntax_Util.head_and_args top  in
           (match uu____1624 with
            | (unary_op,uu____1638) ->
                let head =
                  let _0_320 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (Prims.fst a).FStar_Syntax_Syntax.pos
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    _0_320
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
              FStar_Syntax_Syntax.tk = uu____1699;
              FStar_Syntax_Syntax.pos = uu____1700;
              FStar_Syntax_Syntax.vars = uu____1701;_},(e,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
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
                              (reify_op, [(e, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos
                         in
                      let c =
                        let _0_321 = FStar_Syntax_Syntax.mk_Total repr  in
                        FStar_All.pipe_right _0_321
                          FStar_Syntax_Util.lcomp_of_comp
                         in
                      let uu____1810 = comp_check_expected_typ env e c  in
                      (match uu____1810 with
                       | (e,c,g') ->
                           let _0_322 = FStar_TypeChecker_Rel.conj_guard g g'
                              in
                           (e, c, _0_322)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____1821;
              FStar_Syntax_Syntax.pos = uu____1822;
              FStar_Syntax_Syntax.vars = uu____1823;_},(e,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____1855 =
               Prims.raise
                 (FStar_Errors.Error
                    (let _0_323 =
                       FStar_Util.format1 "Effect %s cannot be reified"
                         l.FStar_Ident.str
                        in
                     (_0_323, (e.FStar_Syntax_Syntax.pos))))
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
                      if uu____1894
                      then no_reflect ()
                      else
                        (let uu____1900 =
                           FStar_TypeChecker_Env.clear_expected_typ env  in
                         match uu____1900 with
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
                                       (let _0_327 =
                                          let _0_326 =
                                            FStar_Syntax_Syntax.as_arg
                                              FStar_Syntax_Syntax.tun
                                             in
                                          let _0_325 =
                                            let _0_324 =
                                              FStar_Syntax_Syntax.as_arg
                                                FStar_Syntax_Syntax.tun
                                               in
                                            [_0_324]  in
                                          _0_326 :: _0_325  in
                                        (repr, _0_327)))) None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____1935 =
                                 let _0_329 =
                                   let _0_328 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env
                                      in
                                   FStar_All.pipe_right _0_328 Prims.fst  in
                                 tc_tot_or_gtot_term _0_329 t  in
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
                                            let _0_330 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation _0_330
                                             in
                                          if uu____2038
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env
                                              [("Expected Tot, got a GTot computation",
                                                 (e.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2044 =
                                            FStar_TypeChecker_Rel.try_teq
                                              env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____2044 with
                                          | None  ->
                                              ((let _0_335 =
                                                  let _0_334 =
                                                    let _0_333 =
                                                      let _0_332 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let _0_331 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        _0_332 _0_331
                                                       in
                                                    (_0_333,
                                                      (e.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [_0_334]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env _0_335);
                                               (let _0_336 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e, _0_336)))
                                          | Some g' ->
                                              let _0_338 =
                                                let _0_337 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' _0_337
                                                 in
                                              (e, _0_338)))
                                     in
                                  (match uu____2025 with
                                   | (e,g) ->
                                       let c =
                                         let _0_343 =
                                           FStar_Syntax_Syntax.mk_Comp
                                             (let _0_342 =
                                                let _0_339 =
                                                  env.FStar_TypeChecker_Env.universe_of
                                                    env res_typ
                                                   in
                                                [_0_339]  in
                                              let _0_341 =
                                                let _0_340 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    wp
                                                   in
                                                [_0_340]  in
                                              {
                                                FStar_Syntax_Syntax.comp_univs
                                                  = _0_342;
                                                FStar_Syntax_Syntax.effect_name
                                                  =
                                                  (ed.FStar_Syntax_Syntax.mname);
                                                FStar_Syntax_Syntax.result_typ
                                                  = res_typ;
                                                FStar_Syntax_Syntax.effect_args
                                                  = _0_341;
                                                FStar_Syntax_Syntax.flags =
                                                  []
                                              })
                                            in
                                         FStar_All.pipe_right _0_343
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
                                         comp_check_expected_typ env e c  in
                                       (match uu____2080 with
                                        | (e,c,g') ->
                                            let _0_344 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e, c, _0_344))))))))
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let env0 = env  in
           let env =
             let _0_346 =
               let _0_345 = FStar_TypeChecker_Env.clear_expected_typ env  in
               FStar_All.pipe_right _0_345 Prims.fst  in
             FStar_All.pipe_right _0_346 instantiate_both  in
           ((let uu____2113 =
               FStar_TypeChecker_Env.debug env FStar_Options.High  in
             if uu____2113
             then
               let _0_348 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let _0_347 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" _0_348 _0_347
             else ());
            (let uu____2115 = tc_term (no_inst env) head  in
             match uu____2115 with
             | (head,chead,g_head) ->
                 let uu____2125 =
                   let uu____2129 =
                     (Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head)
                      in
                   if uu____2129
                   then
                     let _0_349 = FStar_TypeChecker_Env.expected_typ env0  in
                     check_short_circuit_args env head chead g_head args
                       _0_349
                   else
                     (let _0_350 = FStar_TypeChecker_Env.expected_typ env0
                         in
                      check_application_args env head chead g_head args
                        _0_350)
                    in
                 (match uu____2125 with
                  | (e,c,g) ->
                      ((let uu____2141 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Extreme
                           in
                        if uu____2141
                        then
                          let _0_351 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            _0_351
                        else ());
                       (let c =
                          let uu____2144 =
                            ((FStar_TypeChecker_Env.should_verify env) &&
                               (Prims.op_Negation
                                  (FStar_Syntax_Util.is_lcomp_partial_return
                                     c)))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                             in
                          if uu____2144
                          then
                            FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                              env e c
                          else c  in
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
                                  let uu___91_2191 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___91_2191.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___91_2191.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___91_2191.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2216 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let _0_352 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g _0_352  in
                            ((let uu____2219 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____2219
                              then
                                let _0_354 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let _0_353 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  _0_354 _0_353
                              else ());
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
                       | Some t -> (env, t)
                       | None  ->
                           let uu____2277 = FStar_Syntax_Util.type_u ()  in
                           (match uu____2277 with
                            | (k,uu____2283) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env k  in
                                let _0_355 =
                                  FStar_TypeChecker_Env.set_expected_typ env
                                    res_t
                                   in
                                (_0_355, res_t))
                        in
                     (match uu____2271 with
                      | (env_branches,res_t) ->
                          ((let uu____2291 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____2291
                            then
                              let _0_356 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                _0_356
                            else ());
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
                                  (fun uu____2364  ->
                                     fun uu____2365  ->
                                       match (uu____2364, uu____2365) with
                                       | ((uu____2397,f,c,g),(caccum,gaccum))
                                           ->
                                           let _0_357 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), _0_357))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____2345 with
                              | (cases,g) ->
                                  let _0_358 =
                                    FStar_TypeChecker_Util.bind_cases env
                                      res_t cases
                                     in
                                  (_0_358, g)
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
                                           (fun uu____2499  ->
                                              match uu____2499 with
                                              | ((pat,wopt,br),uu____2515,lc,uu____2517)
                                                  ->
                                                  let _0_359 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  (pat, wopt, _0_359)))
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
                                          (e,
                                            (FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.eff_name)))))
                                      None e.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____2562 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____2562
                                  then mk_match e1
                                  else
                                    (let e_match =
                                       mk_match
                                         (FStar_Syntax_Syntax.bv_to_name
                                            guard_x)
                                        in
                                     let lb =
                                       let _0_360 =
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
                                         FStar_Syntax_Syntax.lbeff = _0_360;
                                         FStar_Syntax_Syntax.lbdef = e1
                                       }  in
                                     let e =
                                       (FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_let
                                             (let _0_363 =
                                                let _0_362 =
                                                  let _0_361 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      guard_x
                                                     in
                                                  [_0_361]  in
                                                FStar_Syntax_Subst.close
                                                  _0_362 e_match
                                                 in
                                              ((false, [lb]), _0_363))))
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic env
                                       e cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____2586 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____2586
                                  then
                                    let _0_366 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let _0_365 =
                                      let _0_364 =
                                        cres.FStar_Syntax_Syntax.comp ()  in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        _0_364
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      _0_366 _0_365
                                  else ());
                                 (let _0_367 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e, cres, _0_367))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2590;
                FStar_Syntax_Syntax.lbunivs = uu____2591;
                FStar_Syntax_Syntax.lbtyp = uu____2592;
                FStar_Syntax_Syntax.lbeff = uu____2593;
                FStar_Syntax_Syntax.lbdef = uu____2594;_}::[]),uu____2595)
           ->
           ((let uu____2610 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             if uu____2610
             then
               let _0_368 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" _0_368
             else ());
            check_top_level_let env top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2612),uu____2613) ->
           check_inner_let env top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2623;
                FStar_Syntax_Syntax.lbunivs = uu____2624;
                FStar_Syntax_Syntax.lbtyp = uu____2625;
                FStar_Syntax_Syntax.lbeff = uu____2626;
                FStar_Syntax_Syntax.lbdef = uu____2627;_}::uu____2628),uu____2629)
           ->
           ((let uu____2645 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             if uu____2645
             then
               let _0_369 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" _0_369
             else ());
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
              if uu____2705
              then FStar_Util.Inl t
              else
                FStar_Util.Inr
                  ((let _0_370 = FStar_Syntax_Syntax.mk_Total t  in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      _0_370))
               in
            let is_data_ctor uu___80_2715 =
              match uu___80_2715 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____2718 -> false  in
            let uu____2720 =
              (is_data_ctor dc) &&
                (Prims.op_Negation
                   (FStar_TypeChecker_Env.is_datacon env
                      v.FStar_Syntax_Syntax.v))
               in
            if uu____2720
            then
              Prims.raise
                (FStar_Errors.Error
                   (let _0_372 =
                      FStar_Util.format1
                        "Expected a data constructor; got %s"
                        (v.FStar_Syntax_Syntax.v).FStar_Ident.str
                       in
                    let _0_371 = FStar_TypeChecker_Env.get_range env  in
                    (_0_372, _0_371)))
            else value_check_expected_typ env e tc implicits
         in
      let env = FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          failwith
            (let _0_373 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format1
               "Impossible: Violation of locally nameless convention: %s"
               _0_373)
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____2756 =
              (FStar_Syntax_Subst.compress t1).FStar_Syntax_Syntax.n  in
            match uu____2756 with
            | FStar_Syntax_Syntax.Tm_arrow uu____2757 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____2765 ->
                let imp =
                  ("uvar in term", env, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___92_2785 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___92_2785.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___92_2785.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___92_2785.FStar_TypeChecker_Env.univ_ineqs);
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
                    let _0_376 =
                      let _0_374 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right _0_374
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let _0_375 = FStar_TypeChecker_Rel.conj_guard g0 g1  in
                    (e, _0_376, _0_375)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let t =
            if env.FStar_TypeChecker_Env.use_bv_sorts
            then x.FStar_Syntax_Syntax.sort
            else FStar_TypeChecker_Env.lookup_bv env x  in
          let x =
            let uu___93_2884 = x  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___93_2884.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___93_2884.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = t
            }  in
          (FStar_TypeChecker_Common.insert_bv x t;
           (let e = FStar_Syntax_Syntax.bv_to_name x  in
            let uu____2887 = FStar_TypeChecker_Util.maybe_instantiate env e t
               in
            match uu____2887 with
            | (e,t,implicits) ->
                let tc =
                  let uu____2900 = FStar_TypeChecker_Env.should_verify env
                     in
                  if uu____2900
                  then FStar_Util.Inl t
                  else
                    FStar_Util.Inr
                      ((let _0_377 = FStar_Syntax_Syntax.mk_Total t  in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          _0_377))
                   in
                value_check_expected_typ env e tc implicits))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____2907;
             FStar_Syntax_Syntax.pos = uu____2908;
             FStar_Syntax_Syntax.vars = uu____2909;_},us)
          ->
          let us = FStar_List.map (tc_universe env) us  in
          let uu____2917 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____2917 with
           | (us',t) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_378 = FStar_TypeChecker_Env.get_range env  in
                        ("Unexpected number of universe instantiations",
                          _0_378)))
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____2941 -> failwith "Impossible") us' us;
                (let fv' =
                   let uu___94_2943 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___95_2944 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___95_2944.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___95_2944.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___94_2943.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___94_2943.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e =
                    let _0_379 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst _0_379 us  in
                  check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2978 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____2978 with
           | (us,t) ->
               ((let uu____2991 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Range")
                    in
                 if uu____2991
                 then
                   let _0_384 =
                     FStar_Syntax_Print.lid_to_string
                       (FStar_Syntax_Syntax.lid_of_fv fv)
                      in
                   let _0_383 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let _0_382 =
                     FStar_Range.string_of_range
                       (FStar_Ident.range_of_lid
                          (FStar_Syntax_Syntax.lid_of_fv fv))
                      in
                   let _0_381 =
                     FStar_Range.string_of_use_range
                       (FStar_Ident.range_of_lid
                          (FStar_Syntax_Syntax.lid_of_fv fv))
                      in
                   let _0_380 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s"
                     _0_384 _0_383 _0_382 _0_381 _0_380
                 else ());
                (let fv' =
                   let uu___96_2994 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___97_2995 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___97_2995.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___97_2995.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___96_2994.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___96_2994.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 FStar_TypeChecker_Common.insert_fv fv t;
                 (let e =
                    let _0_385 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst _0_385 us  in
                  check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c  in
          let e =
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
              (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env e (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____3053 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3053 with
           | (bs,c) ->
               let env0 = env  in
               let uu____3062 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____3062 with
                | (env,uu____3070) ->
                    let uu____3073 = tc_binders env bs  in
                    (match uu____3073 with
                     | (bs,env,g,us) ->
                         let uu____3085 = tc_comp env c  in
                         (match uu____3085 with
                          | (c,uc,f) ->
                              let e =
                                let uu___98_3098 =
                                  FStar_Syntax_Util.arrow bs c  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___98_3098.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___98_3098.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___98_3098.FStar_Syntax_Syntax.vars)
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
                                  let _0_386 =
                                    FStar_TypeChecker_Rel.close_guard bs f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g _0_386
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
          let uu____3153 =
            let _0_388 =
              let _0_387 = FStar_Syntax_Syntax.mk_binder x  in [_0_387]  in
            FStar_Syntax_Subst.open_term _0_388 phi  in
          (match uu____3153 with
           | (x,phi) ->
               let env0 = env  in
               let uu____3162 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____3162 with
                | (env,uu____3170) ->
                    let uu____3173 =
                      let _0_389 = FStar_List.hd x  in tc_binder env _0_389
                       in
                    (match uu____3173 with
                     | (x,env,f1,u) ->
                         ((let uu____3194 =
                             FStar_TypeChecker_Env.debug env
                               FStar_Options.High
                              in
                           if uu____3194
                           then
                             let _0_392 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let _0_391 =
                               FStar_Syntax_Print.term_to_string phi  in
                             let _0_390 =
                               FStar_Syntax_Print.bv_to_string (Prims.fst x)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               _0_392 _0_391 _0_390
                           else ());
                          (let uu____3196 = FStar_Syntax_Util.type_u ()  in
                           match uu____3196 with
                           | (t_phi,uu____3203) ->
                               let uu____3204 =
                                 tc_check_tot_or_gtot_term env phi t_phi  in
                               (match uu____3204 with
                                | (phi,uu____3212,f2) ->
                                    let e =
                                      let uu___99_3217 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x) phi
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___99_3217.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___99_3217.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___99_3217.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let _0_393 =
                                        FStar_TypeChecker_Rel.close_guard 
                                          [x] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        _0_393
                                       in
                                    value_check_expected_typ env0 e
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3244) ->
          let bs = FStar_TypeChecker_Util.maybe_add_implicit_binders env bs
             in
          ((let uu____3269 =
              FStar_TypeChecker_Env.debug env FStar_Options.Low  in
            if uu____3269
            then
              let _0_394 =
                FStar_Syntax_Print.term_to_string
                  (let uu___100_3270 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___100_3270.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___100_3270.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___100_3270.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" _0_394
            else ());
           (let uu____3289 = FStar_Syntax_Subst.open_term bs body  in
            match uu____3289 with | (bs,body) -> tc_abs env top bs body))
      | uu____3297 ->
          failwith
            (let _0_396 = FStar_Syntax_Print.term_to_string top  in
             let _0_395 = FStar_Syntax_Print.tag_of_term top  in
             FStar_Util.format2 "Unexpected value: %s (%s)" _0_396 _0_395)

and tc_constant :
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3303 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3304,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3310,Some uu____3311) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3319 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3323 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3324 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3325 ->
          FStar_TypeChecker_Common.t_range
      | uu____3326 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____3337) ->
          let uu____3344 = FStar_Syntax_Util.type_u ()  in
          (match uu____3344 with
           | (k,u) ->
               let uu____3352 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3352 with
                | (t,uu____3360,g) ->
                    let _0_397 = FStar_Syntax_Syntax.mk_Total' t (Some u)  in
                    (_0_397, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3363) ->
          let uu____3370 = FStar_Syntax_Util.type_u ()  in
          (match uu____3370 with
           | (k,u) ->
               let uu____3378 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3378 with
                | (t,uu____3386,g) ->
                    let _0_398 = FStar_Syntax_Syntax.mk_GTotal' t (Some u)
                       in
                    (_0_398, u, g)))
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
            (let _0_400 =
               let _0_399 =
                 FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ
                  in
               _0_399 :: (c.FStar_Syntax_Syntax.effect_args)  in
             FStar_Syntax_Syntax.mk_Tm_app head _0_400) None
              (c.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____3407 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____3407 with
           | (tc,uu____3415,f) ->
               let uu____3417 = FStar_Syntax_Util.head_and_args tc  in
               (match uu____3417 with
                | (head,args) ->
                    let comp_univs =
                      let uu____3447 =
                        (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                         in
                      match uu____3447 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3448,us) -> us
                      | uu____3454 -> []  in
                    let uu____3455 = FStar_Syntax_Util.head_and_args tc  in
                    (match uu____3455 with
                     | (uu____3468,args) ->
                         let uu____3484 =
                           let _0_402 = FStar_List.hd args  in
                           let _0_401 = FStar_List.tl args  in
                           (_0_402, _0_401)  in
                         (match uu____3484 with
                          | (res,args) ->
                              let uu____3536 =
                                let _0_403 =
                                  FStar_All.pipe_right
                                    c.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___81_3554  ->
                                          match uu___81_3554 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____3560 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____3560 with
                                               | (env,uu____3567) ->
                                                   let uu____3570 =
                                                     tc_tot_or_gtot_term env
                                                       e
                                                      in
                                                   (match uu____3570 with
                                                    | (e,uu____3577,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e), g)))
                                          | f ->
                                              (f,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right _0_403 FStar_List.unzip
                                 in
                              (match uu____3536 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (Prims.fst res)
                                      in
                                   let c =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___101_3593 = c  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___101_3593.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (Prims.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___101_3593.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____3597 =
                                       FStar_TypeChecker_Util.effect_repr env
                                         c u
                                        in
                                     match uu____3597 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let _0_404 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c, u_c, _0_404))))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u =
        let u = FStar_Syntax_Subst.compress_univ u  in
        match u with
        | FStar_Syntax_Syntax.U_bvar uu____3607 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  -> u
        | FStar_Syntax_Syntax.U_succ u -> FStar_Syntax_Syntax.U_succ (aux u)
        | FStar_Syntax_Syntax.U_max us ->
            FStar_Syntax_Syntax.U_max (FStar_List.map aux us)
        | FStar_Syntax_Syntax.U_name x -> u  in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let _0_405 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right _0_405 Prims.snd
         | uu____3616 -> aux u)

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
                 (let _0_406 =
                    FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                      env msg t top
                     in
                  (_0_406, (top.FStar_Syntax_Syntax.pos))))
             in
          let check_binders env bs bs_expected =
            let rec aux uu____3690 bs bs_expected =
              match uu____3690 with
              | (env,out,g,subst) ->
                  (match (bs, bs_expected) with
                   | ([],[]) -> (env, (FStar_List.rev out), None, g, subst)
                   | ((hd,imp)::bs,(hd_expected,imp')::bs_expected) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             Prims.raise
                               (FStar_Errors.Error
                                  (let _0_409 =
                                     let _0_407 =
                                       FStar_Syntax_Print.bv_to_string hd  in
                                     FStar_Util.format1
                                       "Inconsistent implicit argument annotation on argument %s"
                                       _0_407
                                      in
                                   let _0_408 =
                                     FStar_Syntax_Syntax.range_of_bv hd  in
                                   (_0_409, _0_408)))
                         | uu____3787 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____3791 =
                           let uu____3794 =
                             (FStar_Syntax_Util.unmeta
                                hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              in
                           match uu____3794 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____3797 ->
                               ((let uu____3799 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.High
                                    in
                                 if uu____3799
                                 then
                                   let _0_410 =
                                     FStar_Syntax_Print.bv_to_string hd  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     _0_410
                                 else ());
                                (let uu____3801 =
                                   tc_tot_or_gtot_term env
                                     hd.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____3801 with
                                 | (t,uu____3808,g1) ->
                                     let g2 =
                                       let _0_412 =
                                         FStar_TypeChecker_Env.get_range env
                                          in
                                       let _0_411 =
                                         FStar_TypeChecker_Rel.teq env t
                                           expected_t
                                          in
                                       FStar_TypeChecker_Util.label_guard
                                         _0_412
                                         "Type annotation on parameter incompatible with the expected type"
                                         _0_411
                                        in
                                     let g =
                                       let _0_413 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         _0_413
                                        in
                                     (t, g)))
                            in
                         match uu____3791 with
                         | (t,g) ->
                             let hd =
                               let uu___102_3827 = hd  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___102_3827.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___102_3827.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env = push_binding env b  in
                             let subst =
                               let _0_414 = FStar_Syntax_Syntax.bv_to_name hd
                                  in
                               maybe_extend_subst subst b_expected _0_414  in
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
                  | uu____3929 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____3933 = tc_binders env bs  in
                  match uu____3933 with
                  | (bs,envbody,g,uu____3952) ->
                      let uu____3953 =
                        let uu____3958 =
                          (FStar_Syntax_Subst.compress body).FStar_Syntax_Syntax.n
                           in
                        match uu____3958 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,FStar_Util.Inr c,uu____3965) ->
                            let uu____3984 = tc_comp envbody c  in
                            (match uu____3984 with
                             | (c,uu____3993,g') ->
                                 let _0_415 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((Some c), body, _0_415))
                        | uu____3996 -> (None, body, g)  in
                      (match uu____3953 with
                       | (copt,body,g) ->
                           (None, bs, [], copt, envbody, body, g))))
            | Some t ->
                let t = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm t =
                  let uu____4046 =
                    (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
                  match uu____4046 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4075 -> failwith "Impossible");
                       (let uu____4079 = tc_binders env bs  in
                        match uu____4079 with
                        | (bs,envbody,g,uu____4099) ->
                            let uu____4100 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____4100 with
                             | (envbody,uu____4117) ->
                                 ((Some (t, true)), bs, [], None, envbody,
                                   body, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4128) ->
                      let uu____4133 =
                        as_function_typ norm b.FStar_Syntax_Syntax.sort  in
                      (match uu____4133 with
                       | (uu____4158,bs,bs',copt,env,body,g) ->
                           ((Some (t, false)), bs, bs', copt, env, body, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4194 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____4194 with
                       | (bs_expected,c_expected) ->
                           let check_actuals_against_formals env bs
                             bs_expected =
                             let rec handle_more uu____4255 c_expected =
                               match uu____4255 with
                               | (env,bs,more,guard,subst) ->
                                   (match more with
                                    | None  ->
                                        let _0_416 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected
                                           in
                                        (env, bs, guard, _0_416)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          FStar_Syntax_Syntax.mk_Total
                                            (FStar_Syntax_Util.arrow
                                               more_bs_expected c_expected)
                                           in
                                        let _0_417 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c
                                           in
                                        (env, bs, guard, _0_417)
                                    | Some (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected
                                           in
                                        if FStar_Syntax_Util.is_named_tot c
                                        then
                                          let t =
                                            unfold_whnf env
                                              (FStar_Syntax_Util.comp_result
                                                 c)
                                             in
                                          (match t.FStar_Syntax_Syntax.n with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected,c_expected) ->
                                               let uu____4372 =
                                                 check_binders env more_bs
                                                   bs_expected
                                                  in
                                               (match uu____4372 with
                                                | (env,bs',more,guard',subst)
                                                    ->
                                                    let _0_419 =
                                                      let _0_418 =
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          guard guard'
                                                         in
                                                      (env,
                                                        (FStar_List.append bs
                                                           bs'), more,
                                                        _0_418, subst)
                                                       in
                                                    handle_more _0_419
                                                      c_expected)
                                           | uu____4407 ->
                                               let _0_421 =
                                                 let _0_420 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t
                                                    in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   _0_420
                                                  in
                                               fail _0_421 t)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t)
                                in
                             let _0_422 = check_binders env bs bs_expected
                                in
                             handle_more _0_422 c_expected  in
                           let mk_letrec_env envbody bs c =
                             let letrecs = guard_letrecs envbody bs c  in
                             let envbody =
                               let uu___103_4445 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___103_4445.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___103_4445.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___103_4445.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___103_4445.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___103_4445.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___103_4445.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___103_4445.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___103_4445.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___103_4445.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___103_4445.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___103_4445.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___103_4445.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___103_4445.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___103_4445.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___103_4445.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___103_4445.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___103_4445.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___103_4445.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___103_4445.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___103_4445.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___103_4445.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___103_4445.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___103_4445.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____4459  ->
                                     fun uu____4460  ->
                                       match (uu____4459, uu____4460) with
                                       | ((env,letrec_binders),(l,t)) ->
                                           let uu____4485 =
                                             let _0_424 =
                                               let _0_423 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env
                                                  in
                                               FStar_All.pipe_right _0_423
                                                 Prims.fst
                                                in
                                             tc_term _0_424 t  in
                                           (match uu____4485 with
                                            | (t,uu____4497,uu____4498) ->
                                                let env =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env l ([], t)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let _0_425 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___104_4505
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___104_4505.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___104_4505.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t
                                                           })
                                                         in
                                                      _0_425 ::
                                                        letrec_binders
                                                  | uu____4506 ->
                                                      letrec_binders
                                                   in
                                                (env, lb))) (envbody, []))
                              in
                           let uu____4509 =
                             check_actuals_against_formals env bs bs_expected
                              in
                           (match uu____4509 with
                            | (envbody,bs,g,c) ->
                                let uu____4539 =
                                  let uu____4543 =
                                    FStar_TypeChecker_Env.should_verify env
                                     in
                                  if uu____4543
                                  then mk_letrec_env envbody bs c
                                  else (envbody, [])  in
                                (match uu____4539 with
                                 | (envbody,letrecs) ->
                                     let envbody =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((Some (t, false)), bs, letrecs,
                                       (Some c), envbody, body, g))))
                  | uu____4576 ->
                      if Prims.op_Negation norm
                      then
                        let _0_426 = unfold_whnf env t  in
                        as_function_typ true _0_426
                      else
                        (let uu____4590 = expected_function_typ env None body
                            in
                         match uu____4590 with
                         | (uu____4614,bs,uu____4616,c_opt,envbody,body,g) ->
                             ((Some (t, false)), bs, [], c_opt, envbody,
                               body, g))
                   in
                as_function_typ false t
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____4637 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____4637 with
          | (env,topt) ->
              ((let uu____4649 =
                  FStar_TypeChecker_Env.debug env FStar_Options.High  in
                if uu____4649
                then
                  let _0_427 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    _0_427
                    (if env.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____4653 = expected_function_typ env topt body  in
                match uu____4653 with
                | (tfun_opt,bs,letrec_binders,c_opt,envbody,body,g) ->
                    let uu____4683 =
                      tc_term
                        (let uu___105_4687 = envbody  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___105_4687.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___105_4687.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___105_4687.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___105_4687.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___105_4687.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___105_4687.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___105_4687.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___105_4687.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___105_4687.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___105_4687.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___105_4687.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___105_4687.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___105_4687.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___105_4687.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___105_4687.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___105_4687.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___105_4687.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___105_4687.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___105_4687.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___105_4687.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___105_4687.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___105_4687.FStar_TypeChecker_Env.qname_and_index)
                         }) body
                       in
                    (match uu____4683 with
                     | (body,cbody,guard_body) ->
                         let guard_body =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         ((let uu____4696 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Implicits")
                              in
                           if uu____4696
                           then
                             let _0_430 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body.FStar_TypeChecker_Env.implicits)
                                in
                             let _0_429 =
                               let _0_428 = cbody.FStar_Syntax_Syntax.comp ()
                                  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string _0_428
                                in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               _0_430 _0_429
                           else ());
                          (let uu____4706 =
                             let _0_432 =
                               let _0_431 = cbody.FStar_Syntax_Syntax.comp ()
                                  in
                               (body, _0_431)  in
                             check_expected_effect
                               (let uu___106_4710 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___106_4710.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___106_4710.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___106_4710.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___106_4710.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___106_4710.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___106_4710.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___106_4710.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___106_4710.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___106_4710.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___106_4710.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___106_4710.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___106_4710.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___106_4710.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___106_4710.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___106_4710.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___106_4710.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___106_4710.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___106_4710.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___106_4710.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___106_4710.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___106_4710.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___106_4710.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___106_4710.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt _0_432
                              in
                           match uu____4706 with
                           | (body,cbody,guard) ->
                               let guard =
                                 FStar_TypeChecker_Rel.conj_guard guard_body
                                   guard
                                  in
                               let guard =
                                 let uu____4721 =
                                   env.FStar_TypeChecker_Env.top_level ||
                                     (Prims.op_Negation
                                        (FStar_TypeChecker_Env.should_verify
                                           env))
                                    in
                                 if uu____4721
                                 then
                                   let _0_433 =
                                     FStar_TypeChecker_Rel.conj_guard g guard
                                      in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody _0_433
                                 else
                                   (let guard =
                                      let _0_434 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard
                                         in
                                      FStar_TypeChecker_Rel.close_guard
                                        (FStar_List.append bs letrec_binders)
                                        _0_434
                                       in
                                    guard)
                                  in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs cbody  in
                               let e =
                                 let _0_437 =
                                   Some
                                     (let _0_436 =
                                        FStar_All.pipe_right
                                          (FStar_Util.dflt cbody c_opt)
                                          FStar_Syntax_Util.lcomp_of_comp
                                         in
                                      FStar_All.pipe_right _0_436
                                        (fun _0_435  -> FStar_Util.Inl _0_435))
                                    in
                                 FStar_Syntax_Util.abs bs body _0_437  in
                               let uu____4743 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t = FStar_Syntax_Subst.compress t
                                        in
                                     (match t.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____4758 -> (e, t, guard)
                                      | uu____4766 ->
                                          let uu____4767 =
                                            if use_teq
                                            then
                                              let _0_438 =
                                                FStar_TypeChecker_Rel.teq env
                                                  t tfun_computed
                                                 in
                                              (e, _0_438)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env e tfun_computed t
                                             in
                                          (match uu____4767 with
                                           | (e,guard') ->
                                               let _0_439 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard guard'
                                                  in
                                               (e, t, _0_439)))
                                 | None  -> (e, tfun_computed, guard)  in
                               (match uu____4743 with
                                | (e,tfun,guard) ->
                                    let c =
                                      if env.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env tfun e
                                       in
                                    let uu____4790 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env e
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard
                                       in
                                    (match uu____4790 with
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
              (let uu____4826 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____4826
               then
                 let _0_441 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos
                    in
                 let _0_440 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" _0_441 _0_440
               else ());
              (let monadic_application uu____4868 subst arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____4868 with
                 | (head,chead,ghead,cres) ->
                     let rt =
                       check_no_escape (Some head) env fvs
                         cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres =
                       let uu___107_4909 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___107_4909.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___107_4909.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___107_4909.FStar_Syntax_Syntax.comp)
                       }  in
                     let uu____4910 =
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
                                     (fun uu___82_4937  ->
                                        match uu___82_4937 with
                                        | (uu____4946,uu____4947,FStar_Util.Inl
                                           uu____4948) -> false
                                        | (uu____4959,uu____4960,FStar_Util.Inr
                                           c) ->
                                            Prims.op_Negation
                                              (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 c))))
                              in
                           let cres =
                             if refine_with_equality
                             then
                               let _0_442 =
                                 (FStar_Syntax_Syntax.mk_Tm_app head
                                    (FStar_List.rev arg_rets))
                                   (Some
                                      ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                   r
                                  in
                               FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                 env _0_442 cres
                             else
                               ((let uu____4983 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____4983
                                 then
                                   let _0_445 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let _0_444 =
                                     FStar_Syntax_Print.lcomp_to_string cres
                                      in
                                   let _0_443 =
                                     FStar_TypeChecker_Rel.guard_to_string
                                       env g
                                      in
                                   FStar_Util.print3
                                     "Not refining result: f=%s; cres=%s; guard=%s\n"
                                     _0_445 _0_444 _0_443
                                 else ());
                                cres)
                              in
                           (cres, g)
                       | uu____4985 ->
                           let g =
                             let _0_446 =
                               FStar_TypeChecker_Rel.conj_guard ghead guard
                                in
                             FStar_All.pipe_right _0_446
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let _0_450 =
                             let _0_449 =
                               FStar_Syntax_Syntax.mk_Total
                                 (let _0_448 =
                                    let _0_447 =
                                      cres.FStar_Syntax_Syntax.comp ()  in
                                    FStar_Syntax_Util.arrow bs _0_447  in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.subst subst) _0_448)
                                in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp _0_449
                              in
                           (_0_450, g)
                        in
                     (match uu____4910 with
                      | (cres,guard) ->
                          ((let uu____4998 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____4998
                            then
                              let _0_451 =
                                FStar_Syntax_Print.lcomp_to_string cres  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" _0_451
                            else ());
                           (let uu____5000 =
                              FStar_List.fold_left
                                (fun uu____5023  ->
                                   fun uu____5024  ->
                                     match (uu____5023, uu____5024) with
                                     | ((args,out_c,monadic),((e,q),x,c)) ->
                                         (match c with
                                          | FStar_Util.Inl (eff_name,arg_typ)
                                              ->
                                              let _0_454 =
                                                let _0_453 =
                                                  let _0_452 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env e eff_name
                                                      out_c.FStar_Syntax_Syntax.eff_name
                                                      arg_typ
                                                     in
                                                  (_0_452, q)  in
                                                _0_453 :: args  in
                                              (_0_454, out_c, monadic)
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
                            match uu____5000 with
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
                                  let uu____5159 =
                                    monadic ||
                                      (Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                            comp))
                                     in
                                  if uu____5159
                                  then
                                    FStar_TypeChecker_Util.maybe_monadic env
                                      app comp.FStar_Syntax_Syntax.eff_name
                                      comp.FStar_Syntax_Syntax.res_typ
                                  else app  in
                                let uu____5161 =
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    None env app comp guard
                                   in
                                (match uu____5161 with
                                 | (comp,g) -> (app, comp, g)))))
                  in
               let rec tc_args head_info uu____5219 bs args =
                 match uu____5219 with
                 | (subst,outargs,arg_rets,g,fvs) ->
                     (match (bs, args) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____5314))::rest,
                         (uu____5316,None )::uu____5317) ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t = check_no_escape (Some head) env fvs t  in
                          let uu____5354 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head.FStar_Syntax_Syntax.pos env t
                             in
                          (match uu____5354 with
                           | (varg,uu____5365,implicits) ->
                               let subst = (FStar_Syntax_Syntax.NT (x, varg))
                                 :: subst  in
                               let arg =
                                 let _0_455 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, _0_455)  in
                               let _0_457 =
                                 let _0_456 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t))) :: outargs), (arg ::
                                   arg_rets), _0_456, fvs)
                                  in
                               tc_args head_info _0_457 rest args)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____5468 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x =
                              let uu___108_5475 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___108_5475.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___108_5475.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____5477 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____5477
                             then
                               let _0_458 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n" _0_458
                             else ());
                            (let targ =
                               check_no_escape (Some head) env fvs targ  in
                             let env =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ
                                in
                             let env =
                               let uu___109_5482 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___109_5482.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___109_5482.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___109_5482.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___109_5482.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___109_5482.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___109_5482.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___109_5482.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___109_5482.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___109_5482.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___109_5482.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___109_5482.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___109_5482.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___109_5482.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___109_5482.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___109_5482.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___109_5482.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___109_5482.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___109_5482.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___109_5482.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___109_5482.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___109_5482.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___109_5482.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___109_5482.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             (let uu____5484 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.High
                                 in
                              if uu____5484
                              then
                                let _0_461 = FStar_Syntax_Print.tag_of_term e
                                   in
                                let _0_460 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let _0_459 =
                                  FStar_Syntax_Print.term_to_string targ  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n" _0_461
                                  _0_460 _0_459
                              else ());
                             (let uu____5486 = tc_term env e  in
                              match uu____5486 with
                              | (e,c,g_e) ->
                                  let g =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e, aq)  in
                                  let uu____5502 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c
                                     in
                                  if uu____5502
                                  then
                                    let subst =
                                      let _0_462 = FStar_List.hd bs  in
                                      maybe_extend_subst subst _0_462 e  in
                                    tc_args head_info
                                      (subst,
                                        ((arg, None,
                                           (FStar_Util.Inl
                                              ((c.FStar_Syntax_Syntax.eff_name),
                                                (c.FStar_Syntax_Syntax.res_typ))))
                                        :: outargs), (arg :: arg_rets), g,
                                        fvs) rest rest'
                                  else
                                    (let uu____5562 =
                                       FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env c.FStar_Syntax_Syntax.eff_name
                                        in
                                     if uu____5562
                                     then
                                       let subst =
                                         let _0_463 = FStar_List.hd bs  in
                                         maybe_extend_subst subst _0_463 e
                                          in
                                       tc_args head_info
                                         (subst,
                                           ((arg, (Some x),
                                              (FStar_Util.Inr c)) ::
                                           outargs), (arg :: arg_rets), g,
                                           fvs) rest rest'
                                     else
                                       (let uu____5612 =
                                          FStar_Syntax_Syntax.is_null_binder
                                            (FStar_List.hd bs)
                                           in
                                        if uu____5612
                                        then
                                          let newx =
                                            FStar_Syntax_Syntax.new_bv
                                              (Some
                                                 (e.FStar_Syntax_Syntax.pos))
                                              c.FStar_Syntax_Syntax.res_typ
                                             in
                                          let arg' =
                                            let _0_464 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                newx
                                               in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              _0_464
                                             in
                                          tc_args head_info
                                            (subst,
                                              ((arg, (Some newx),
                                                 (FStar_Util.Inr c)) ::
                                              outargs), (arg' :: arg_rets),
                                              g, fvs) rest rest'
                                        else
                                          (let _0_467 =
                                             let _0_466 =
                                               let _0_465 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   (FStar_Syntax_Syntax.bv_to_name
                                                      x)
                                                  in
                                               _0_465 :: arg_rets  in
                                             (subst,
                                               ((arg, (Some x),
                                                  (FStar_Util.Inr c)) ::
                                               outargs), _0_466, g, (x ::
                                               fvs))
                                              in
                                           tc_args head_info _0_467 rest
                                             rest')))))))
                      | (uu____5694,[]) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____5715) ->
                          let uu____5745 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs []
                             in
                          (match uu____5745 with
                           | (head,chead,ghead) ->
                               let rec aux norm tres =
                                 let tres =
                                   let _0_468 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right _0_468
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,cres') ->
                                     let uu____5783 =
                                       FStar_Syntax_Subst.open_comp bs cres'
                                        in
                                     (match uu____5783 with
                                      | (bs,cres') ->
                                          let head_info =
                                            (head, chead, ghead,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'))
                                             in
                                          ((let uu____5797 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____5797
                                            then
                                              let _0_469 =
                                                FStar_Range.string_of_range
                                                  tres.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                _0_469
                                            else ());
                                           tc_args head_info
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs args))
                                 | uu____5827 when Prims.op_Negation norm ->
                                     let _0_470 = unfold_whnf env tres  in
                                     aux true _0_470
                                 | uu____5828 ->
                                     Prims.raise
                                       (FStar_Errors.Error
                                          (let _0_474 =
                                             let _0_472 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env thead
                                                in
                                             let _0_471 =
                                               FStar_Util.string_of_int
                                                 n_args
                                                in
                                             FStar_Util.format2
                                               "Too many arguments to function of type %s; got %s arguments"
                                               _0_472 _0_471
                                              in
                                           let _0_473 =
                                             FStar_Syntax_Syntax.argpos arg
                                              in
                                           (_0_474, _0_473)))
                                  in
                               aux false chead.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app norm tf =
                 let uu____5847 =
                   (FStar_Syntax_Util.unrefine tf).FStar_Syntax_Syntax.n  in
                 match uu____5847 with
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
                           let uu____5921 = tc_term env e  in
                           (match uu____5921 with
                            | (e,c,g_e) ->
                                let uu____5934 = tc_args env tl  in
                                (match uu____5934 with
                                 | (args,comps,g_rest) ->
                                     let _0_475 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e, imp) :: args),
                                       (((e.FStar_Syntax_Syntax.pos), c) ::
                                       comps), _0_475)))
                        in
                     let uu____5966 = tc_args env args  in
                     (match uu____5966 with
                      | (args,comps,g_args) ->
                          let bs =
                            FStar_Syntax_Util.null_binders_of_tks
                              (FStar_All.pipe_right comps
                                 (FStar_List.map
                                    (fun uu____6004  ->
                                       match uu____6004 with
                                       | (uu____6012,c) ->
                                           ((c.FStar_Syntax_Syntax.res_typ),
                                             None))))
                             in
                          let ml_or_tot t r =
                            let uu____6028 = FStar_Options.ml_ish ()  in
                            if uu____6028
                            then FStar_Syntax_Util.ml_comp t r
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let _0_478 =
                              let _0_477 =
                                let _0_476 = FStar_Syntax_Util.type_u ()  in
                                FStar_All.pipe_right _0_476 Prims.fst  in
                              FStar_TypeChecker_Util.new_uvar env _0_477  in
                            ml_or_tot _0_478 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____6037 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____6037
                            then
                              let _0_481 =
                                FStar_Syntax_Print.term_to_string head  in
                              let _0_480 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let _0_479 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                _0_481 _0_480 _0_479
                            else ());
                           (let _0_482 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              _0_482);
                           (let comp =
                              let _0_483 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____6043  ->
                                   fun out  ->
                                     match uu____6043 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head.FStar_Syntax_Syntax.pos), chead) ::
                                comps) _0_483
                               in
                            let _0_485 =
                              (FStar_Syntax_Syntax.mk_Tm_app head args)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r
                               in
                            let _0_484 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (_0_485, comp, _0_484))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____6074 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____6074 with
                      | (bs,c) ->
                          let head_info =
                            (head, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c))
                             in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs args)
                 | uu____6117 ->
                     if Prims.op_Negation norm
                     then
                       let _0_486 = unfold_whnf env tf  in
                       check_function_app true _0_486
                     else
                       Prims.raise
                         (FStar_Errors.Error
                            (let _0_487 =
                               FStar_TypeChecker_Err.expected_function_typ
                                 env tf
                                in
                             (_0_487, (head.FStar_Syntax_Syntax.pos))))
                  in
               let _0_489 =
                 let _0_488 = FStar_Syntax_Util.unrefine thead  in
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.WHNF] env _0_488
                  in
               check_function_app false _0_489)

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
                  let uu____6174 =
                    FStar_List.fold_left2
                      (fun uu____6187  ->
                         fun uu____6188  ->
                           fun uu____6189  ->
                             match (uu____6187, uu____6188, uu____6189) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____6233 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____6233 with
                                   | (e,c,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen
                                          in
                                       let g =
                                         let _0_490 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           _0_490 g
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
                                       let _0_494 =
                                         let _0_492 =
                                           let _0_491 =
                                             FStar_Syntax_Syntax.as_arg e  in
                                           [_0_491]  in
                                         FStar_List.append seen _0_492  in
                                       let _0_493 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g
                                          in
                                       (_0_494, _0_493, ghost))))
                      ([], g_head, false) args bs
                     in
                  (match uu____6174 with
                   | (args,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head args)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r
                          in
                       let c =
                         if ghost
                         then
                           let _0_495 = FStar_Syntax_Syntax.mk_GTotal res_t
                              in
                           FStar_All.pipe_right _0_495
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____6279 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c guard
                          in
                       (match uu____6279 with | (c,g) -> (e, c, g)))
              | uu____6291 ->
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
        let uu____6313 = FStar_Syntax_Subst.open_branch branch  in
        match uu____6313 with
        | (pattern,when_clause,branch_exp) ->
            let uu____6339 = branch  in
            (match uu____6339 with
             | (cpat,uu____6359,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____6401 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0
                      in
                   match uu____6401 with
                   | (pat_bvs,exps,p) ->
                       ((let uu____6423 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____6423
                         then
                           let _0_497 = FStar_Syntax_Print.pat_to_string p0
                              in
                           let _0_496 = FStar_Syntax_Print.pat_to_string p
                              in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             _0_497 _0_496
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs
                            in
                         let uu____6426 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____6426 with
                         | (env1,uu____6439) ->
                             let env1 =
                               let uu___110_6443 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___110_6443.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___110_6443.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___110_6443.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___110_6443.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___110_6443.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___110_6443.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___110_6443.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___110_6443.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___110_6443.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___110_6443.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___110_6443.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___110_6443.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___110_6443.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___110_6443.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___110_6443.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___110_6443.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___110_6443.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___110_6443.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___110_6443.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___110_6443.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___110_6443.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___110_6443.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___110_6443.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             let uu____6445 =
                               let _0_513 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____6465 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High
                                             in
                                          if uu____6465
                                          then
                                            let _0_499 =
                                              FStar_Syntax_Print.term_to_string
                                                e
                                               in
                                            let _0_498 =
                                              FStar_Syntax_Print.term_to_string
                                                pat_t
                                               in
                                            FStar_Util.print2
                                              "Checking pattern expression %s against expected type %s\n"
                                              _0_499 _0_498
                                          else ());
                                         (let uu____6467 = tc_term env1 e  in
                                          match uu____6467 with
                                          | (e,lc,g) ->
                                              ((let uu____6477 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High
                                                   in
                                                if uu____6477
                                                then
                                                  let _0_501 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env e
                                                     in
                                                  let _0_500 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  FStar_Util.print2
                                                    "Pre-checked pattern expression %s at type %s\n"
                                                    _0_501 _0_500
                                                else ());
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
                                                let uu____6481 =
                                                  let _0_502 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___111_6482 = g
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___111_6482.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___111_6482.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___111_6482.FStar_TypeChecker_Env.implicits)
                                                       })
                                                     in
                                                  FStar_All.pipe_right _0_502
                                                    FStar_TypeChecker_Rel.resolve_implicits
                                                   in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e
                                                   in
                                                let uvars_to_string uvs =
                                                  let _0_504 =
                                                    let _0_503 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements
                                                       in
                                                    FStar_All.pipe_right
                                                      _0_503
                                                      (FStar_List.map
                                                         (fun uu____6516  ->
                                                            match uu____6516
                                                            with
                                                            | (u,uu____6521)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u))
                                                     in
                                                  FStar_All.pipe_right _0_504
                                                    (FStar_String.concat ", ")
                                                   in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e'
                                                   in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t
                                                   in
                                                (let uu____6533 =
                                                   let _0_505 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2
                                                      in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation _0_505
                                                    in
                                                 if uu____6533
                                                 then
                                                   let unresolved =
                                                     let _0_506 =
                                                       FStar_Util.set_difference
                                                         uvs1 uvs2
                                                        in
                                                     FStar_All.pipe_right
                                                       _0_506
                                                       FStar_Util.set_elements
                                                      in
                                                   Prims.raise
                                                     (FStar_Errors.Error
                                                        (let _0_511 =
                                                           let _0_510 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e'
                                                              in
                                                           let _0_509 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env
                                                               expected_pat_t
                                                              in
                                                           let _0_508 =
                                                             let _0_507 =
                                                               FStar_All.pipe_right
                                                                 unresolved
                                                                 (FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____6561
                                                                     ->
                                                                    match uu____6561
                                                                    with
                                                                    | 
                                                                    (u,uu____6569)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u))
                                                                in
                                                             FStar_All.pipe_right
                                                               _0_507
                                                               (FStar_String.concat
                                                                  ", ")
                                                              in
                                                           FStar_Util.format3
                                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                             _0_510 _0_509
                                                             _0_508
                                                            in
                                                         (_0_511,
                                                           (p.FStar_Syntax_Syntax.p))))
                                                 else ());
                                                (let uu____6583 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High
                                                    in
                                                 if uu____6583
                                                 then
                                                   let _0_512 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env e
                                                      in
                                                   FStar_Util.print1
                                                     "Done checking pattern expression %s\n"
                                                     _0_512
                                                 else ());
                                                (e, e'))))))
                                  in
                               FStar_All.pipe_right _0_513 FStar_List.unzip
                                in
                             (match uu____6445 with
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
                 let uu____6607 =
                   let _0_514 = FStar_TypeChecker_Env.push_bv env scrutinee
                      in
                   FStar_All.pipe_right _0_514
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____6607 with
                  | (scrutinee_env,uu____6623) ->
                      let uu____6626 = tc_pat true pat_t pattern  in
                      (match uu____6626 with
                       | (pattern,pat_bvs,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____6654 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____6669 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____6669
                                 then
                                   Prims.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____6677 =
                                      let _0_515 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool
                                         in
                                      tc_term _0_515 e  in
                                    match uu____6677 with
                                    | (e,c,g) -> ((Some e), g))
                              in
                           (match uu____6654 with
                            | (when_clause,g_when) ->
                                let uu____6700 = tc_term pat_env branch_exp
                                   in
                                (match uu____6700 with
                                 | (branch_exp,c,g_branch) ->
                                     let when_condition =
                                       match when_clause with
                                       | None  -> None
                                       | Some w ->
                                           let _0_517 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_516  -> Some _0_516)
                                             _0_517
                                        in
                                     let uu____6720 =
                                       let eqs =
                                         let uu____6726 =
                                           Prims.op_Negation
                                             (FStar_TypeChecker_Env.should_verify
                                                env)
                                            in
                                         if uu____6726
                                         then None
                                         else
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
                                                     | uu____6740 ->
                                                         let clause =
                                                           let _0_518 =
                                                             env.FStar_TypeChecker_Env.universe_of
                                                               env pat_t
                                                              in
                                                           FStar_Syntax_Util.mk_eq2
                                                             _0_518 pat_t
                                                             scrutinee_tm e
                                                            in
                                                         (match fopt with
                                                          | None  ->
                                                              Some clause
                                                          | Some f ->
                                                              let _0_520 =
                                                                FStar_Syntax_Util.mk_disj
                                                                  clause f
                                                                 in
                                                              FStar_All.pipe_left
                                                                (fun _0_519 
                                                                   ->
                                                                   Some
                                                                    _0_519)
                                                                _0_520)) None)
                                          in
                                       let uu____6751 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp c g_branch
                                          in
                                       match uu____6751 with
                                       | (c,g_branch) ->
                                           let uu____6761 =
                                             match (eqs, when_condition) with
                                             | uu____6768 when
                                                 Prims.op_Negation
                                                   (FStar_TypeChecker_Env.should_verify
                                                      env)
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
                                                 let _0_522 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c gf
                                                    in
                                                 let _0_521 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (_0_522, _0_521)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     (FStar_Syntax_Util.mk_conj
                                                        f w)
                                                    in
                                                 let _0_525 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c g_fw
                                                    in
                                                 let _0_524 =
                                                   let _0_523 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     _0_523 g_when
                                                    in
                                                 (_0_525, _0_524)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let _0_526 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c g_w
                                                    in
                                                 (_0_526, g_when)
                                              in
                                           (match uu____6761 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs
                                                   in
                                                let _0_528 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs c_weak
                                                   in
                                                let _0_527 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    binders g_when_weak
                                                   in
                                                (_0_528, _0_527, g_branch))
                                        in
                                     (match uu____6720 with
                                      | (c,g_when,g_branch) ->
                                          let branch_guard =
                                            let uu____6810 =
                                              Prims.op_Negation
                                                (FStar_TypeChecker_Env.should_verify
                                                   env)
                                               in
                                            if uu____6810
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm pat_exp =
                                                 let discriminate
                                                   scrutinee_tm f =
                                                   let uu____6841 =
                                                     let _0_530 =
                                                       FStar_List.length
                                                         (Prims.snd
                                                            (let _0_529 =
                                                               FStar_TypeChecker_Env.typ_of_datacon
                                                                 env
                                                                 f.FStar_Syntax_Syntax.v
                                                                in
                                                             FStar_TypeChecker_Env.datacons_of_typ
                                                               env _0_529))
                                                        in
                                                     _0_530 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____6841
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____6852 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____6852 with
                                                     | None  -> []
                                                     | uu____6859 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None
                                                            in
                                                         let disc =
                                                           (let _0_532 =
                                                              let _0_531 =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  scrutinee_tm
                                                                 in
                                                              [_0_531]  in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              disc _0_532)
                                                             None
                                                             scrutinee_tm.FStar_Syntax_Syntax.pos
                                                            in
                                                         let _0_533 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc
                                                             FStar_Syntax_Const.exp_true_bool
                                                            in
                                                         [_0_533]
                                                   else []  in
                                                 let fail uu____6878 =
                                                   failwith
                                                     (let _0_536 =
                                                        FStar_Range.string_of_range
                                                          pat_exp.FStar_Syntax_Syntax.pos
                                                         in
                                                      let _0_535 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp
                                                         in
                                                      let _0_534 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        _0_536 _0_535 _0_534)
                                                    in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t,uu____6899) ->
                                                       head_constructor t
                                                   | uu____6905 -> fail ()
                                                    in
                                                 let pat_exp =
                                                   let _0_537 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp
                                                      in
                                                   FStar_All.pipe_right
                                                     _0_537
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
                                                     c ->
                                                     let _0_539 =
                                                       let _0_538 =
                                                         tc_constant
                                                           pat_exp.FStar_Syntax_Syntax.pos
                                                           c
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         _0_538 scrutinee_tm
                                                         pat_exp
                                                        in
                                                     [_0_539]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                   _
                                                   |FStar_Syntax_Syntax.Tm_fvar
                                                   _ ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp
                                                        in
                                                     let uu____6931 =
                                                       Prims.op_Negation
                                                         (FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v)
                                                        in
                                                     if uu____6931
                                                     then []
                                                     else
                                                       (let _0_540 =
                                                          head_constructor
                                                            pat_exp
                                                           in
                                                        discriminate
                                                          scrutinee_tm _0_540)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head,args) ->
                                                     let f =
                                                       head_constructor head
                                                        in
                                                     let uu____6961 =
                                                       Prims.op_Negation
                                                         (FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v)
                                                        in
                                                     if uu____6961
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let _0_544 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____6986
                                                                     ->
                                                                    match uu____6986
                                                                    with
                                                                    | 
                                                                    (ei,uu____6993)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____7003
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____7003
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____7010
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    (let _0_543
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None  in
                                                                    let _0_542
                                                                    =
                                                                    let _0_541
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm
                                                                     in
                                                                    [_0_541]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    _0_543
                                                                    _0_542)
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            _0_544
                                                            FStar_List.flatten
                                                           in
                                                        let _0_545 =
                                                          discriminate
                                                            scrutinee_tm f
                                                           in
                                                        FStar_List.append
                                                          _0_545
                                                          sub_term_guards)
                                                 | uu____7031 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm pat =
                                                 let uu____7043 =
                                                   Prims.op_Negation
                                                     (FStar_TypeChecker_Env.should_verify
                                                        env)
                                                    in
                                                 if uu____7043
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let _0_546 =
                                                        build_branch_guard
                                                          scrutinee_tm pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        _0_546
                                                       in
                                                    let uu____7047 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____7047 with
                                                    | (k,uu____7051) ->
                                                        let uu____7052 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____7052
                                                         with
                                                         | (t,uu____7057,uu____7058)
                                                             -> t))
                                                  in
                                               let branch_guard =
                                                 let _0_547 =
                                                   FStar_All.pipe_right
                                                     norm_disj_exps
                                                     (FStar_List.map
                                                        (build_and_check_branch_guard
                                                           scrutinee_tm))
                                                    in
                                                 FStar_All.pipe_right _0_547
                                                   FStar_Syntax_Util.mk_disj_l
                                                  in
                                               let branch_guard =
                                                 match when_condition with
                                                 | None  -> branch_guard
                                                 | Some w ->
                                                     FStar_Syntax_Util.mk_conj
                                                       branch_guard w
                                                  in
                                               branch_guard)
                                             in
                                          let guard =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when g_branch
                                             in
                                          ((let uu____7069 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____7069
                                            then
                                              let _0_548 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                _0_548
                                            else ());
                                           (let _0_549 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern, when_clause,
                                                  branch_exp)
                                               in
                                            (_0_549, branch_guard, c, guard)))))))))

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
          let uu____7088 = check_let_bound_def true env lb  in
          (match uu____7088 with
           | (e1,univ_vars,c1,g1,annotated) ->
               let uu____7102 =
                 if
                   annotated &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then (g1, e1, univ_vars, c1)
                 else
                   (let g1 =
                      let _0_550 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env
                          g1
                         in
                      FStar_All.pipe_right _0_550
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____7114 =
                      FStar_List.hd
                        (let _0_553 =
                           let _0_552 =
                             let _0_551 = c1.FStar_Syntax_Syntax.comp ()  in
                             ((lb.FStar_Syntax_Syntax.lbname), e1, _0_551)
                              in
                           [_0_552]  in
                         FStar_TypeChecker_Util.generalize env _0_553)
                       in
                    match uu____7114 with
                    | (uu____7145,univs,e1,c1) ->
                        (g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1)))
                  in
               (match uu____7102 with
                | (g1,e1,univ_vars,c1) ->
                    let uu____7156 =
                      let uu____7161 =
                        FStar_TypeChecker_Env.should_verify env  in
                      if uu____7161
                      then
                        let uu____7166 =
                          FStar_TypeChecker_Util.check_top_level env g1 c1
                           in
                        match uu____7166 with
                        | (ok,c1) ->
                            (if ok
                             then (e2, c1)
                             else
                               ((let uu____7183 =
                                   FStar_Options.warn_top_level_effects ()
                                    in
                                 if uu____7183
                                 then
                                   let _0_554 =
                                     FStar_TypeChecker_Env.get_range env  in
                                   FStar_Errors.warn _0_554
                                     FStar_TypeChecker_Err.top_level_effect
                                 else ());
                                (let _0_555 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos
                                    in
                                 (_0_555, c1))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                         (let c =
                            let _0_556 = c1.FStar_Syntax_Syntax.comp ()  in
                            FStar_All.pipe_right _0_556
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env)
                             in
                          let e2 =
                            let uu____7209 = FStar_Syntax_Util.is_pure_comp c
                               in
                            if uu____7209
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos
                             in
                          (e2, c)))
                       in
                    (match uu____7156 with
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
                           let _0_557 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb]), e2)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos
                              in
                           (_0_557, (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____7261 -> failwith "Impossible"

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
            let uu___112_7282 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___112_7282.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___112_7282.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___112_7282.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___112_7282.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___112_7282.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___112_7282.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___112_7282.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___112_7282.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___112_7282.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___112_7282.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___112_7282.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___112_7282.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___112_7282.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___112_7282.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___112_7282.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___112_7282.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___112_7282.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___112_7282.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___112_7282.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___112_7282.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___112_7282.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___112_7282.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___112_7282.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____7283 =
            let _0_559 =
              let _0_558 = FStar_TypeChecker_Env.clear_expected_typ env  in
              FStar_All.pipe_right _0_558 Prims.fst  in
            check_let_bound_def false _0_559 lb  in
          (match uu____7283 with
           | (e1,uu____7297,c1,g1,annotated) ->
               let x =
                 let uu___113_7302 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___113_7302.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___113_7302.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 }  in
               let uu____7303 =
                 let _0_561 =
                   let _0_560 = FStar_Syntax_Syntax.mk_binder x  in [_0_560]
                    in
                 FStar_Syntax_Subst.open_term _0_561 e2  in
               (match uu____7303 with
                | (xb,e2) ->
                    let xbinder = FStar_List.hd xb  in
                    let x = Prims.fst xbinder  in
                    let uu____7317 =
                      let _0_562 = FStar_TypeChecker_Env.push_bv env x  in
                      tc_term _0_562 e2  in
                    (match uu____7317 with
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
                                 (let _0_563 = FStar_Syntax_Subst.close xb e2
                                     in
                                  ((false, [lb]), _0_563))))
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
                           let _0_567 =
                             let _0_566 =
                               env.FStar_TypeChecker_Env.universe_of env
                                 c1.FStar_Syntax_Syntax.res_typ
                                in
                             let _0_565 = FStar_Syntax_Syntax.bv_to_name x
                                in
                             FStar_Syntax_Util.mk_eq2 _0_566
                               c1.FStar_Syntax_Syntax.res_typ _0_565 e1
                              in
                           FStar_All.pipe_left
                             (fun _0_564  ->
                                FStar_TypeChecker_Common.NonTrivial _0_564)
                             _0_567
                            in
                         let g2 =
                           let _0_569 =
                             let _0_568 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard _0_568 g2  in
                           FStar_TypeChecker_Rel.close_guard xb _0_569  in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g2
                            in
                         let uu____7351 =
                           FStar_Option.isSome
                             (FStar_TypeChecker_Env.expected_typ env)
                            in
                         if uu____7351
                         then
                           let tt =
                             let _0_570 =
                               FStar_TypeChecker_Env.expected_typ env  in
                             FStar_All.pipe_right _0_570 FStar_Option.get  in
                           ((let uu____7358 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____7358
                             then
                               let _0_572 =
                                 FStar_Syntax_Print.term_to_string tt  in
                               let _0_571 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 _0_572 _0_571
                             else ());
                            (e, cres, guard))
                         else
                           (let t =
                              check_no_escape None env [x]
                                cres.FStar_Syntax_Syntax.res_typ
                               in
                            (let uu____7363 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____7363
                             then
                               let _0_574 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               let _0_573 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 _0_574 _0_573
                             else ());
                            (e,
                              ((let uu___114_7365 = cres  in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___114_7365.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___114_7365.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___114_7365.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____7366 -> failwith "Impossible"

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
          let uu____7387 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____7387 with
           | (lbs,e2) ->
               let uu____7398 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____7398 with
                | (env0,topt) ->
                    let uu____7409 = build_let_rec_env true env0 lbs  in
                    (match uu____7409 with
                     | (lbs,rec_env) ->
                         let uu____7420 = check_let_recs rec_env lbs  in
                         (match uu____7420 with
                          | (lbs,g_lbs) ->
                              let g_lbs =
                                let _0_575 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env g_lbs
                                   in
                                FStar_All.pipe_right _0_575
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let _0_577 =
                                  FStar_All.pipe_right lbs
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right _0_577
                                  (fun _0_576  -> Some _0_576)
                                 in
                              let lbs =
                                if
                                  Prims.op_Negation
                                    env.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs
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
                                     let _0_579 =
                                       FStar_All.pipe_right lbs
                                         (FStar_List.map
                                            (fun lb  ->
                                               let _0_578 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 _0_578)))
                                        in
                                     FStar_TypeChecker_Util.generalize env
                                       _0_579
                                      in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____7493  ->
                                           match uu____7493 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e)))
                                 in
                              let cres =
                                let _0_580 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp _0_580
                                 in
                              (FStar_ST.write e2.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____7524 =
                                  FStar_Syntax_Subst.close_let_rec lbs e2  in
                                match uu____7524 with
                                | (lbs,e2) ->
                                    let _0_582 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs), e2)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let _0_581 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env g_lbs
                                       in
                                    (_0_582, cres, _0_581)))))))
      | uu____7553 -> failwith "Impossible"

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
          let uu____7574 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____7574 with
           | (lbs,e2) ->
               let uu____7585 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____7585 with
                | (env0,topt) ->
                    let uu____7596 = build_let_rec_env false env0 lbs  in
                    (match uu____7596 with
                     | (lbs,rec_env) ->
                         let uu____7607 = check_let_recs rec_env lbs  in
                         (match uu____7607 with
                          | (lbs,g_lbs) ->
                              let uu____7618 =
                                FStar_All.pipe_right lbs
                                  (FStar_Util.fold_map
                                     (fun env  ->
                                        fun lb  ->
                                          let x =
                                            let uu___115_7629 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___115_7629.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___115_7629.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb =
                                            let uu___116_7631 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___116_7631.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___116_7631.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___116_7631.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___116_7631.FStar_Syntax_Syntax.lbdef)
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
                              (match uu____7618 with
                               | (env,lbs) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____7648 = tc_term env e2  in
                                   (match uu____7648 with
                                    | (e2,cres,g2) ->
                                        let guard =
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
                                          let uu___117_7662 = cres  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___117_7662.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___117_7662.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___117_7662.FStar_Syntax_Syntax.comp)
                                          }  in
                                        let uu____7663 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs e2
                                           in
                                        (match uu____7663 with
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
                                              | Some uu____7692 ->
                                                  (e, cres, guard)
                                              | None  ->
                                                  let tres =
                                                    check_no_escape None env
                                                      bvs tres
                                                     in
                                                  let cres =
                                                    let uu___118_7697 = cres
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___118_7697.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___118_7697.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___118_7697.FStar_Syntax_Syntax.comp)
                                                    }  in
                                                  (e, cres, guard)))))))))
      | uu____7700 -> failwith "Impossible"

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
          let uu____7716 = FStar_Syntax_Util.arrow_formals_comp t  in
          match uu____7716 with
          | (uu____7722,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c)
                 in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)
           in
        let uu____7733 =
          FStar_List.fold_left
            (fun uu____7740  ->
               fun lb  ->
                 match uu____7740 with
                 | (lbs,env) ->
                     let uu____7752 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env
                         lb
                        in
                     (match uu____7752 with
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
                            if Prims.op_Negation check_t
                            then t
                            else
                              (let uu____7766 =
                                 let _0_584 =
                                   let _0_583 = FStar_Syntax_Util.type_u ()
                                      in
                                   FStar_All.pipe_left Prims.fst _0_583  in
                                 tc_check_tot_or_gtot_term
                                   (let uu___119_7770 = env0  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___119_7770.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___119_7770.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___119_7770.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___119_7770.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___119_7770.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___119_7770.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___119_7770.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___119_7770.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___119_7770.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___119_7770.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___119_7770.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___119_7770.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___119_7770.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___119_7770.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___119_7770.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___119_7770.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___119_7770.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___119_7770.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___119_7770.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___119_7770.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___119_7770.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___119_7770.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___119_7770.FStar_TypeChecker_Env.qname_and_index)
                                    }) t _0_584
                                  in
                               match uu____7766 with
                               | (t,uu____7774,g) ->
                                   let g =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let _0_585 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env g
                                        in
                                     FStar_All.pipe_left Prims.ignore _0_585);
                                    norm env0 t))
                             in
                          let env =
                            let uu____7779 =
                              (termination_check_enabled t) &&
                                (FStar_TypeChecker_Env.should_verify env)
                               in
                            if uu____7779
                            then
                              let uu___120_7780 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___120_7780.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___120_7780.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___120_7780.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___120_7780.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___120_7780.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___120_7780.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___120_7780.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___120_7780.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___120_7780.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___120_7780.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___120_7780.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___120_7780.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t) ::
                                  (env.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___120_7780.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___120_7780.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___120_7780.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___120_7780.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___120_7780.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___120_7780.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___120_7780.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___120_7780.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___120_7780.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___120_7780.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___120_7780.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env
                                lb.FStar_Syntax_Syntax.lbname ([], t)
                             in
                          let lb =
                            let uu___121_7790 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___121_7790.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars;
                              FStar_Syntax_Syntax.lbtyp = t;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___121_7790.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb :: lbs), env))) ([], env) lbs
           in
        match uu____7733 with | (lbs,env) -> ((FStar_List.rev lbs), env)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____7804 =
        let _0_587 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____7823 =
                    let _0_586 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    tc_tot_or_gtot_term _0_586 lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____7823 with
                  | (e,c,g) ->
                      ((let uu____7833 =
                          Prims.op_Negation
                            (FStar_Syntax_Util.is_total_lcomp c)
                           in
                        if uu____7833
                        then
                          Prims.raise
                            (FStar_Errors.Error
                               ("Expected let rec to be a Tot term; got effect GTot",
                                 (e.FStar_Syntax_Syntax.pos)))
                        else ());
                       (let lb =
                          FStar_Syntax_Util.mk_letbinding
                            lb.FStar_Syntax_Syntax.lbname
                            lb.FStar_Syntax_Syntax.lbunivs
                            lb.FStar_Syntax_Syntax.lbtyp
                            FStar_Syntax_Const.effect_Tot_lid e
                           in
                        (lb, g)))))
           in
        FStar_All.pipe_right _0_587 FStar_List.unzip  in
      match uu____7804 with
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
        let uu____7855 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____7855 with
        | (env1,uu____7865) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____7871 = check_lbtyp top_level env lb  in
            (match uu____7871 with
             | (topt,wf_annot,univ_vars,univ_opening,env1) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e1 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____7897 =
                     tc_maybe_toplevel_term
                       (let uu___122_7901 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___122_7901.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___122_7901.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___122_7901.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___122_7901.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___122_7901.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___122_7901.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___122_7901.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___122_7901.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___122_7901.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___122_7901.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___122_7901.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___122_7901.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___122_7901.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___122_7901.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___122_7901.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___122_7901.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___122_7901.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___122_7901.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___122_7901.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___122_7901.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___122_7901.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___122_7901.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___122_7901.FStar_TypeChecker_Env.qname_and_index)
                        }) e1
                      in
                   match uu____7897 with
                   | (e1,c1,g1) ->
                       let uu____7910 =
                         let _0_588 =
                           FStar_TypeChecker_Env.set_range env1
                             e1.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____7915  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           _0_588 e1 c1 wf_annot
                          in
                       (match uu____7910 with
                        | (c1,guard_f) ->
                            let g1 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____7925 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____7925
                              then
                                let _0_591 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let _0_590 =
                                  FStar_Syntax_Print.term_to_string
                                    c1.FStar_Syntax_Syntax.res_typ
                                   in
                                let _0_589 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1
                                   in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  _0_591 _0_590 _0_589
                              else ());
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
        | uu____7951 ->
            let uu____7952 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____7952 with
             | (univ_opening,univ_vars) ->
                 let t = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let _0_592 = FStar_TypeChecker_Env.set_expected_typ env1 t
                      in
                   ((Some t), FStar_TypeChecker_Rel.trivial_guard, univ_vars,
                     univ_opening, _0_592)
                 else
                   (let uu____7983 = FStar_Syntax_Util.type_u ()  in
                    match uu____7983 with
                    | (k,uu____7994) ->
                        let uu____7995 = tc_check_tot_or_gtot_term env1 t k
                           in
                        (match uu____7995 with
                         | (t,uu____8007,g) ->
                             ((let uu____8010 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____8010
                               then
                                 let _0_594 =
                                   FStar_Range.string_of_range
                                     (FStar_Syntax_Syntax.range_of_lbname
                                        lb.FStar_Syntax_Syntax.lbname)
                                    in
                                 let _0_593 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n" _0_594
                                   _0_593
                               else ());
                              (let t = norm env1 t  in
                               let _0_595 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t
                                  in
                               ((Some t), g, univ_vars, univ_opening, _0_595))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____8017  ->
      match uu____8017 with
      | (x,imp) ->
          let uu____8028 = FStar_Syntax_Util.type_u ()  in
          (match uu____8028 with
           | (tu,u) ->
               ((let uu____8040 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____8040
                 then
                   let _0_598 = FStar_Syntax_Print.bv_to_string x  in
                   let _0_597 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let _0_596 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     _0_598 _0_597 _0_596
                 else ());
                (let uu____8042 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____8042 with
                 | (t,uu____8053,g) ->
                     let x =
                       ((let uu___123_8058 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___123_8058.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___123_8058.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____8060 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____8060
                       then
                         let _0_600 =
                           FStar_Syntax_Print.bv_to_string (Prims.fst x)  in
                         let _0_599 = FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           _0_600 _0_599
                       else ());
                      (let _0_601 = push_binding env x  in (x, _0_601, g, u))))))

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
            let uu____8112 = tc_binder env b  in
            (match uu____8112 with
             | (b,env',g,u) ->
                 let uu____8135 = aux env' bs  in
                 (match uu____8135 with
                  | (bs,env',g',us) ->
                      let _0_603 =
                        let _0_602 = FStar_TypeChecker_Rel.close_guard [b] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g _0_602  in
                      ((b :: bs), env', _0_603, (u :: us))))
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
          (fun uu____8206  ->
             fun uu____8207  ->
               match (uu____8206, uu____8207) with
               | ((t,imp),(args,g)) ->
                   let uu____8244 = tc_term env t  in
                   (match uu____8244 with
                    | (t,uu____8254,g') ->
                        let _0_604 = FStar_TypeChecker_Rel.conj_guard g g'
                           in
                        (((t, imp) :: args), _0_604))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____8273  ->
             match uu____8273 with
             | (pats,g) ->
                 let uu____8287 = tc_args env p  in
                 (match uu____8287 with
                  | (args,g') ->
                      let _0_605 = FStar_TypeChecker_Rel.conj_guard g g'  in
                      ((args :: pats), _0_605))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____8302 = tc_maybe_toplevel_term env e  in
      match uu____8302 with
      | (e,c,g) ->
          let uu____8312 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____8312
          then (e, c, g)
          else
            (let g = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c = c.FStar_Syntax_Syntax.comp ()  in
             let c = norm_c env c  in
             let uu____8322 =
               let uu____8325 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c)
                  in
               if uu____8325
               then
                 let _0_606 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c)
                    in
                 (_0_606, false)
               else
                 (let _0_607 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c)
                     in
                  (_0_607, true))
                in
             match uu____8322 with
             | (target_comp,allow_ghost) ->
                 let uu____8334 =
                   FStar_TypeChecker_Rel.sub_comp env c target_comp  in
                 (match uu____8334 with
                  | Some g' ->
                      let _0_608 = FStar_TypeChecker_Rel.conj_guard g g'  in
                      (e, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        _0_608)
                  | uu____8340 ->
                      if allow_ghost
                      then
                        Prims.raise
                          (FStar_Errors.Error
                             (let _0_609 =
                                FStar_TypeChecker_Err.expected_ghost_expression
                                  e c
                                 in
                              (_0_609, (e.FStar_Syntax_Syntax.pos))))
                      else
                        Prims.raise
                          (FStar_Errors.Error
                             (let _0_610 =
                                FStar_TypeChecker_Err.expected_pure_expression
                                  e c
                                 in
                              (_0_610, (e.FStar_Syntax_Syntax.pos))))))

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
      let uu____8361 = tc_tot_or_gtot_term env t  in
      match uu____8361 with
      | (t,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; (t, c))

let type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      (let uu____8381 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____8381
       then
         let _0_611 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" _0_611
       else ());
      (let env =
         let uu___124_8384 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___124_8384.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___124_8384.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___124_8384.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___124_8384.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___124_8384.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___124_8384.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___124_8384.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___124_8384.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___124_8384.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___124_8384.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___124_8384.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___124_8384.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___124_8384.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___124_8384.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___124_8384.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___124_8384.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___124_8384.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___124_8384.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___124_8384.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___124_8384.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___124_8384.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____8387 =
         try tc_tot_or_gtot_term env e
         with
         | FStar_Errors.Error (msg,uu____8403) ->
             Prims.raise
               (FStar_Errors.Error
                  (let _0_612 = FStar_TypeChecker_Env.get_range env  in
                   ((Prims.strcat "Implicit argument: " msg), _0_612)))
          in
       match uu____8387 with
       | (t,c,g) ->
           let uu____8413 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____8413
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             Prims.raise
               (FStar_Errors.Error
                  (let _0_615 =
                     let _0_613 = FStar_Syntax_Print.term_to_string e  in
                     FStar_Util.format1
                       "Implicit argument: Expected a total term; got a ghost term: %s"
                       _0_613
                      in
                   let _0_614 = FStar_TypeChecker_Env.get_range env  in
                   (_0_615, _0_614))))
  
let level_of_type_fail env e t =
  Prims.raise
    (FStar_Errors.Error
       (let _0_618 =
          let _0_616 = FStar_Syntax_Print.term_to_string e  in
          FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
            _0_616 t
           in
        let _0_617 = FStar_TypeChecker_Env.get_range env  in (_0_618, _0_617)))
  
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t =
          let uu____8456 =
            (FStar_Syntax_Util.unrefine t).FStar_Syntax_Syntax.n  in
          match uu____8456 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____8458 ->
              if retry
              then
                let t =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t
                   in
                aux false t
              else
                (let uu____8461 = FStar_Syntax_Util.type_u ()  in
                 match uu____8461 with
                 | (t_u,u) ->
                     let env =
                       let uu___127_8467 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___127_8467.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___127_8467.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___127_8467.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___127_8467.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___127_8467.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___127_8467.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___127_8467.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___127_8467.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___127_8467.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___127_8467.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___127_8467.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___127_8467.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___127_8467.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___127_8467.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___127_8467.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___127_8467.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___127_8467.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___127_8467.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___127_8467.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___127_8467.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___127_8467.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___127_8467.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___127_8467.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env t t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let _0_619 = FStar_Syntax_Print.term_to_string t
                              in
                           level_of_type_fail env e _0_619
                       | uu____8471 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env g);
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
      let uu____8480 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
         in
      match uu____8480 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____8487 ->
          let e = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____8498) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____8523,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____8538) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____8545 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8545 with | (uu____8554,t) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____8556,FStar_Util.Inl t,uu____8558) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____8577,FStar_Util.Inr c,uu____8579) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____8609;
             FStar_Syntax_Syntax.pos = uu____8610;
             FStar_Syntax_Syntax.vars = uu____8611;_},us)
          ->
          let uu____8617 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8617 with
           | (us',t) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_620 = FStar_TypeChecker_Env.get_range env  in
                        ("Unexpected number of universe instantiations",
                          _0_620)))
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____8640 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____8641 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____8649) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____8666 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8666 with
           | (bs,c) ->
               let us =
                 FStar_List.map
                   (fun uu____8677  ->
                      match uu____8677 with
                      | (b,uu____8681) ->
                          let _0_621 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort _0_621)
                   bs
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c  in
                 let _0_622 = universe_of_aux env res  in
                 level_of_type env res _0_622  in
               let u_c =
                 let uu____8687 =
                   FStar_TypeChecker_Util.effect_repr env c u_res  in
                 match uu____8687 with
                 | None  -> u_res
                 | Some trepr ->
                     let _0_623 = universe_of_aux env trepr  in
                     level_of_type env trepr _0_623
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
                -> let _0_624 = universe_of_aux env hd  in (_0_624, args)
            | FStar_Syntax_Syntax.Tm_match (uu____8782,hd::uu____8784) ->
                let uu____8831 = FStar_Syntax_Subst.open_branch hd  in
                (match uu____8831 with
                 | (uu____8841,uu____8842,hd) ->
                     let uu____8858 = FStar_Syntax_Util.head_and_args hd  in
                     (match uu____8858 with
                      | (hd,args) -> type_of_head retry hd args))
            | uu____8893 when retry ->
                let e =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____8895 = FStar_Syntax_Util.head_and_args e  in
                (match uu____8895 with
                 | (hd,args) -> type_of_head false hd args)
            | uu____8930 ->
                let uu____8931 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                (match uu____8931 with
                 | (env,uu____8945) ->
                     let env =
                       let uu___128_8949 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___128_8949.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___128_8949.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___128_8949.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___128_8949.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___128_8949.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___128_8949.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___128_8949.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___128_8949.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___128_8949.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___128_8949.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___128_8949.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___128_8949.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___128_8949.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___128_8949.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___128_8949.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___128_8949.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___128_8949.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___128_8949.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___128_8949.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___128_8949.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___128_8949.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     ((let uu____8951 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____8951
                       then
                         let _0_626 =
                           FStar_Range.string_of_range
                             (FStar_TypeChecker_Env.get_range env)
                            in
                         let _0_625 = FStar_Syntax_Print.term_to_string hd
                            in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           _0_626 _0_625
                       else ());
                      (let uu____8953 = tc_term env hd  in
                       match uu____8953 with
                       | (uu____8966,{
                                       FStar_Syntax_Syntax.eff_name =
                                         uu____8967;
                                       FStar_Syntax_Syntax.res_typ = t;
                                       FStar_Syntax_Syntax.cflags =
                                         uu____8969;
                                       FStar_Syntax_Syntax.comp = uu____8970;_},g)
                           ->
                           ((let _0_627 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env g
                                in
                             FStar_All.pipe_right _0_627 Prims.ignore);
                            (t, args)))))
             in
          let uu____8987 = type_of_head true hd args  in
          (match uu____8987 with
           | (t,args) ->
               let t =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____9016 = FStar_Syntax_Util.arrow_formals_comp t  in
               (match uu____9016 with
                | (bs,res) ->
                    let res = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args  in
                      FStar_Syntax_Subst.subst subst res
                    else
                      (let _0_628 = FStar_Syntax_Print.term_to_string res  in
                       level_of_type_fail env e _0_628)))
      | FStar_Syntax_Syntax.Tm_match (uu____9051,hd::uu____9053) ->
          let uu____9100 = FStar_Syntax_Subst.open_branch hd  in
          (match uu____9100 with
           | (uu____9103,uu____9104,hd) -> universe_of_aux env hd)
      | FStar_Syntax_Syntax.Tm_match (uu____9120,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let _0_629 = universe_of_aux env e  in level_of_type env e _0_629
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____9166 = tc_binders env tps  in
      match uu____9166 with
      | (tps,env,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (tps, env, us))
  