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
      (fun v  ->
         fun tl  ->
           let r =
             if tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos
                 tl.FStar_Syntax_Syntax.pos
              in
           (let _0_264 =
              let _0_263 = FStar_Syntax_Syntax.as_arg v  in
              let _0_262 =
                let _0_261 = FStar_Syntax_Syntax.as_arg tl  in [_0_261]  in
              _0_263 :: _0_262  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _0_264)
             (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r) vs
      FStar_Syntax_Util.lex_top
  
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.bool =
  fun uu___77_41  ->
    match uu___77_41 with
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
                                let _0_265 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  _0_265
                            | Some head ->
                                let _0_267 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let _0_266 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  _0_267 _0_266
                             in
                          Prims.raise
                            (FStar_Errors.Error
                               (let _0_268 =
                                  FStar_TypeChecker_Env.get_range env  in
                                (msg, _0_268)))
                           in
                        let s =
                          let _0_270 =
                            let _0_269 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left Prims.fst _0_269  in
                          FStar_TypeChecker_Util.new_uvar env _0_270  in
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
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun t  ->
        let uu___84_166 = lc  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (uu___84_166.FStar_Syntax_Syntax.lcomp_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (uu___84_166.FStar_Syntax_Syntax.lcomp_univs);
          FStar_Syntax_Syntax.lcomp_indices =
            (uu___84_166.FStar_Syntax_Syntax.lcomp_indices);
          FStar_Syntax_Syntax.lcomp_res_typ = t;
          FStar_Syntax_Syntax.lcomp_cflags =
            (uu___84_166.FStar_Syntax_Syntax.lcomp_cflags);
          FStar_Syntax_Syntax.lcomp_as_comp =
            (fun uu____167  ->
               let _0_271 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
               FStar_TypeChecker_Env.set_result_typ env _0_271 t)
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
            let uu____204 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            match uu____204 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____205,c) ->
                let uu____217 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                if uu____217
                then
                  let t =
                    let _0_272 = FStar_TypeChecker_Env.result_typ env c  in
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine _0_272  in
                  let uu____219 =
                    (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
                  (match uu____219 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____221 -> false
                   | uu____222 -> true)
                else false
            | uu____224 -> true  in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let _0_273 =
                  let uu____227 =
                    (Prims.op_Negation (should_return t)) ||
                      (Prims.op_Negation
                         (FStar_TypeChecker_Env.should_verify env))
                     in
                  if uu____227
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e  in
                FStar_TypeChecker_Env.lcomp_of_comp env _0_273
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.lcomp_res_typ  in
          let uu____233 =
            let uu____237 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____237 with
            | None  -> let _0_274 = memo_tk e t  in (_0_274, lc, guard)
            | Some t' ->
                ((let uu____244 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High  in
                  if uu____244
                  then
                    let _0_276 = FStar_Syntax_Print.term_to_string t  in
                    let _0_275 = FStar_Syntax_Print.term_to_string t'  in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" _0_276
                      _0_275
                  else ());
                 (let uu____246 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t'
                     in
                  match uu____246 with
                  | (e,lc) ->
                      let t = lc.FStar_Syntax_Syntax.lcomp_res_typ  in
                      let uu____257 =
                        FStar_TypeChecker_Util.check_and_ascribe env e t t'
                         in
                      (match uu____257 with
                       | (e,g) ->
                           ((let uu____266 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____266
                             then
                               let _0_280 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let _0_279 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let _0_278 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let _0_277 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 _0_280 _0_279 _0_278 _0_277
                             else ());
                            (let msg =
                               let uu____272 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               if uu____272
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_281  -> Some _0_281)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t t')
                                in
                             let g = FStar_TypeChecker_Rel.conj_guard g guard
                                in
                             let uu____287 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e lc g
                                in
                             match uu____287 with
                             | (lc,g) ->
                                 let _0_282 = memo_tk e t'  in
                                 (_0_282, (set_lcomp_result env lc t'), g))))))
             in
          match uu____233 with
          | (e,lc,g) ->
              ((let uu____302 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                if uu____302
                then
                  let _0_283 = FStar_Syntax_Print.lcomp_to_string lc  in
                  FStar_Util.print1 "Return comp type is %s\n" _0_283
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
        let uu____319 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____319 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____325 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____325 with
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
      fun uu____347  ->
        match uu____347 with
        | (e,c) ->
            let expected_c_opt =
              match copt with
              | Some uu____362 -> copt
              | None  ->
                  let uu____363 =
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
                  if uu____363
                  then
                    Some
                      (let _0_284 = FStar_TypeChecker_Env.result_typ env c
                          in
                       FStar_Syntax_Util.ml_comp _0_284
                         e.FStar_Syntax_Syntax.pos)
                  else
                    (let uu____366 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____366
                     then None
                     else
                       (let uu____369 = FStar_Syntax_Util.is_pure_comp c  in
                        if uu____369
                        then
                          Some
                            (FStar_Syntax_Syntax.mk_Total
                               (FStar_TypeChecker_Env.result_typ env c))
                        else
                          (let uu____372 =
                             FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                           if uu____372
                           then
                             Some
                               (FStar_Syntax_Syntax.mk_GTotal
                                  (FStar_TypeChecker_Env.result_typ env c))
                           else None)))
               in
            (match expected_c_opt with
             | None  ->
                 let _0_285 = norm_c env c  in
                 (e, _0_285, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____380 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                   if uu____380
                   then
                     let _0_288 = FStar_Syntax_Print.term_to_string e  in
                     let _0_287 = FStar_Syntax_Print.comp_to_string c  in
                     let _0_286 =
                       FStar_Syntax_Print.comp_to_string expected_c  in
                     FStar_Util.print3
                       "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                       _0_288 _0_287 _0_286
                   else ());
                  (let c = norm_c env c  in
                   (let uu____384 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                    if uu____384
                    then
                      let _0_291 = FStar_Syntax_Print.term_to_string e  in
                      let _0_290 = FStar_Syntax_Print.comp_to_string c  in
                      let _0_289 =
                        FStar_Syntax_Print.comp_to_string expected_c  in
                      FStar_Util.print3
                        "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                        _0_291 _0_290 _0_289
                    else ());
                   (let uu____386 =
                      FStar_TypeChecker_Util.check_comp env e c expected_c
                       in
                    match uu____386 with
                    | (e,uu____394,g) ->
                        let g =
                          let _0_292 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_TypeChecker_Util.label_guard _0_292
                            "could not prove post-condition" g
                           in
                        ((let uu____398 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low
                             in
                          if uu____398
                          then
                            let _0_294 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos
                               in
                            let _0_293 =
                              FStar_TypeChecker_Rel.guard_to_string env g  in
                            FStar_Util.print2
                              "(%s) DONE check_expected_effect; guard is: %s\n"
                              _0_294 _0_293
                          else ());
                         (let e =
                            let _0_295 =
                              FStar_TypeChecker_Env.result_typ env c  in
                            FStar_TypeChecker_Util.maybe_lift env e
                              (FStar_Syntax_Util.comp_effect_name c)
                              (FStar_Syntax_Util.comp_effect_name expected_c)
                              _0_295
                             in
                          (e, expected_c, g)))))))
  
let no_logical_guard env uu____420 =
  match uu____420 with
  | (te,kt,f) ->
      let uu____427 = FStar_TypeChecker_Rel.guard_form f  in
      (match uu____427 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f ->
           Prims.raise
             (FStar_Errors.Error
                (let _0_297 =
                   FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                     env f
                    in
                 let _0_296 = FStar_TypeChecker_Env.get_range env  in
                 (_0_297, _0_296))))
  
let print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____438 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____438 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let _0_298 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" _0_298
  
let check_smt_pat env t bs c =
  let uu____475 = FStar_Syntax_Util.is_smt_lemma t  in
  if uu____475
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_typ_name = uu____476;
          FStar_Syntax_Syntax.comp_univs = uu____477;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____481)::[];
          FStar_Syntax_Syntax.flags = uu____482;_}
        ->
        let pat_vars =
          FStar_Syntax_Free.names
            (FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta] env pats)
           in
        let uu____514 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____526  ->
                  match uu____526 with
                  | (b,uu____530) ->
                      Prims.op_Negation (FStar_Util.set_mem b pat_vars)))
           in
        (match uu____514 with
         | None  -> ()
         | Some (x,uu____534) ->
             let _0_300 =
               let _0_299 = FStar_Syntax_Print.bv_to_string x  in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" _0_299
                in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos _0_300)
    | uu____537 -> failwith "Impossible"
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
        let uu____558 =
          Prims.op_Negation (FStar_TypeChecker_Env.should_verify env)  in
        if uu____558
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env  in
               let env =
                 let uu___85_576 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___85_576.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___85_576.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___85_576.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___85_576.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___85_576.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___85_576.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___85_576.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___85_576.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___85_576.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___85_576.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___85_576.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___85_576.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___85_576.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___85_576.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___85_576.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___85_576.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___85_576.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___85_576.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___85_576.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___85_576.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___85_576.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___85_576.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___85_576.FStar_TypeChecker_Env.qname_and_index)
                 }  in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env
                   FStar_Syntax_Const.precedes_lid
                  in
               let decreases_clause bs c =
                 let filter_types_and_functions bs =
                   FStar_All.pipe_right bs
                     (FStar_List.collect
                        (fun uu____599  ->
                           match uu____599 with
                           | (b,uu____604) ->
                               let t =
                                 let _0_301 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort
                                    in
                                 unfold_whnf env _0_301  in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type _
                                  |FStar_Syntax_Syntax.Tm_arrow _ -> []
                                | uu____609 ->
                                    let _0_302 =
                                      FStar_Syntax_Syntax.bv_to_name b  in
                                    [_0_302])))
                    in
                 let as_lex_list dec =
                   let uu____614 = FStar_Syntax_Util.head_and_args dec  in
                   match uu____614 with
                   | (head,uu____625) ->
                       (match head.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____641 -> mk_lex_list [dec])
                    in
                 let cflags = FStar_Syntax_Util.comp_flags c  in
                 let uu____644 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___78_648  ->
                           match uu___78_648 with
                           | FStar_Syntax_Syntax.DECREASES uu____649 -> true
                           | uu____652 -> false))
                    in
                 match uu____644 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____656 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions  in
                     (match xs with
                      | x::[] -> x
                      | uu____662 -> mk_lex_list xs)
                  in
               let previous_dec = decreases_clause actuals expected_c  in
               let guard_one_letrec uu____672 =
                 match uu____672 with
                 | (l,t) ->
                     let uu____679 =
                       (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                        in
                     (match uu____679 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____708  ->
                                    match uu____708 with
                                    | (x,imp) ->
                                        let uu____715 =
                                          FStar_Syntax_Syntax.is_null_bv x
                                           in
                                        if uu____715
                                        then
                                          let _0_304 =
                                            let _0_303 =
                                              Some
                                                (FStar_Syntax_Syntax.range_of_bv
                                                   x)
                                               in
                                            FStar_Syntax_Syntax.new_bv _0_303
                                              x.FStar_Syntax_Syntax.sort
                                             in
                                          (_0_304, imp)
                                        else (x, imp)))
                             in
                          let uu____719 =
                            FStar_Syntax_Subst.open_comp formals c  in
                          (match uu____719 with
                           | (formals,c) ->
                               let dec = decreases_clause formals c  in
                               let precedes =
                                 (let _0_308 =
                                    let _0_307 =
                                      FStar_Syntax_Syntax.as_arg dec  in
                                    let _0_306 =
                                      let _0_305 =
                                        FStar_Syntax_Syntax.as_arg
                                          previous_dec
                                         in
                                      [_0_305]  in
                                    _0_307 :: _0_306  in
                                  FStar_Syntax_Syntax.mk_Tm_app precedes
                                    _0_308) None r
                                  in
                               let uu____734 = FStar_Util.prefix formals  in
                               (match uu____734 with
                                | (bs,(last,imp)) ->
                                    let last =
                                      let uu___86_758 = last  in
                                      let _0_309 =
                                        FStar_Syntax_Util.refine last
                                          precedes
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___86_758.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___86_758.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = _0_309
                                      }  in
                                    let refined_formals =
                                      FStar_List.append bs [(last, imp)]  in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c
                                       in
                                    ((let uu____771 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Low
                                         in
                                      if uu____771
                                      then
                                        let _0_312 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l
                                           in
                                        let _0_311 =
                                          FStar_Syntax_Print.term_to_string t
                                           in
                                        let _0_310 =
                                          FStar_Syntax_Print.term_to_string
                                            t'
                                           in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          _0_312 _0_311 _0_310
                                      else ());
                                     (l, t'))))
                      | uu____773 ->
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
        (let uu___87_1031 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___87_1031.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___87_1031.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___87_1031.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___87_1031.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___87_1031.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___87_1031.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___87_1031.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___87_1031.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___87_1031.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___87_1031.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___87_1031.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___87_1031.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___87_1031.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___87_1031.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___87_1031.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___87_1031.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___87_1031.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___87_1031.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___87_1031.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___87_1031.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___87_1031.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___87_1031.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___87_1031.FStar_TypeChecker_Env.qname_and_index)
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
      (let uu____1040 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       if uu____1040
       then
         let _0_315 =
           let _0_313 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range _0_313  in
         let _0_314 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" _0_315 _0_314
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1046 -> failwith "Impossible"
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
           let uu____1085 = tc_tot_or_gtot_term env e  in
           (match uu____1085 with
            | (e,c,g) ->
                let g =
                  let uu___88_1096 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___88_1096.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___88_1096.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___88_1096.FStar_TypeChecker_Env.implicits)
                  }  in
                (e, c, g))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1109 = FStar_Syntax_Util.type_u ()  in
           (match uu____1109 with
            | (t,u) ->
                let uu____1117 = tc_check_tot_or_gtot_term env e t  in
                (match uu____1117 with
                 | (e,c,g) ->
                     let uu____1127 =
                       let uu____1136 =
                         FStar_TypeChecker_Env.clear_expected_typ env  in
                       match uu____1136 with
                       | (env,uu____1149) -> tc_pats env pats  in
                     (match uu____1127 with
                      | (pats,g') ->
                          let g' =
                            let uu___89_1170 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___89_1170.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___89_1170.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___89_1170.FStar_TypeChecker_Env.implicits)
                            }  in
                          let _0_317 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e,
                                    (FStar_Syntax_Syntax.Meta_pattern pats))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let _0_316 = FStar_TypeChecker_Rel.conj_guard g g'
                             in
                          (_0_317, c, _0_316))))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1190 =
             (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n  in
           (match uu____1190 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1194,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1196;
                               FStar_Syntax_Syntax.lbtyp = uu____1197;
                               FStar_Syntax_Syntax.lbeff = uu____1198;
                               FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
                ->
                let uu____1216 =
                  let _0_318 =
                    FStar_TypeChecker_Env.set_expected_typ env
                      FStar_TypeChecker_Common.t_unit
                     in
                  tc_term _0_318 e1  in
                (match uu____1216 with
                 | (e1,c1,g1) ->
                     let uu____1226 = tc_term env e2  in
                     (match uu____1226 with
                      | (e2,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind env (Some e1) c1
                              (None, c2)
                             in
                          let e =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_let
                                  (let _0_321 =
                                     let _0_320 =
                                       let _0_319 =
                                         FStar_Syntax_Syntax.mk_lb
                                           (x, [],
                                             (c1.FStar_Syntax_Syntax.lcomp_name),
                                             FStar_TypeChecker_Common.t_unit,
                                             e1)
                                          in
                                       [_0_319]  in
                                     (false, _0_320)  in
                                   (_0_321, e2))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e,
                                    (FStar_Syntax_Syntax.Meta_desugared
                                       FStar_Syntax_Syntax.Sequence))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let _0_322 = FStar_TypeChecker_Rel.conj_guard g1 g2
                             in
                          (e, c, _0_322)))
            | uu____1273 ->
                let uu____1274 = tc_term env e  in
                (match uu____1274 with
                 | (e,c,g) ->
                     let e =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (e,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Sequence))))
                         (Some
                            ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e,FStar_Syntax_Syntax.Meta_monadic uu____1298) -> tc_term env e
       | FStar_Syntax_Syntax.Tm_meta (e,m) ->
           let uu____1313 = tc_term env e  in
           (match uu____1313 with
            | (e,c,g) ->
                let e =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos
                   in
                (e, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e,FStar_Util.Inr expected_c,uu____1338) ->
           let uu____1357 = FStar_TypeChecker_Env.clear_expected_typ env  in
           (match uu____1357 with
            | (env0,uu____1365) ->
                let uu____1368 = tc_comp env0 expected_c  in
                (match uu____1368 with
                 | (expected_c,uu____1376,g) ->
                     let t_res =
                       FStar_TypeChecker_Env.result_typ env expected_c  in
                     let uu____1379 =
                       let _0_323 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term _0_323 e  in
                     (match uu____1379 with
                      | (e,c',g') ->
                          let uu____1389 =
                            let _0_325 =
                              let _0_324 =
                                c'.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                              (e, _0_324)  in
                            check_expected_effect env0 (Some expected_c)
                              _0_325
                             in
                          (match uu____1389 with
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
                                 FStar_TypeChecker_Env.lcomp_of_comp env
                                   expected_c
                                  in
                               let f =
                                 let _0_326 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g _0_326
                                  in
                               let uu____1421 =
                                 comp_check_expected_typ env e lc  in
                               (match uu____1421 with
                                | (e,c,f2) ->
                                    let _0_327 =
                                      FStar_TypeChecker_Rel.conj_guard f f2
                                       in
                                    (e, c, _0_327))))))
       | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t,uu____1433) ->
           let uu____1452 = FStar_Syntax_Util.type_u ()  in
           (match uu____1452 with
            | (k,u) ->
                let uu____1460 = tc_check_tot_or_gtot_term env t k  in
                (match uu____1460 with
                 | (t,uu____1468,f) ->
                     let uu____1470 =
                       let _0_328 =
                         FStar_TypeChecker_Env.set_expected_typ env t  in
                       tc_term _0_328 e  in
                     (match uu____1470 with
                      | (e,c,g) ->
                          let uu____1480 =
                            let _0_329 =
                              FStar_TypeChecker_Env.set_range env
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1485  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              _0_329 e c f
                             in
                          (match uu____1480 with
                           | (c,f) ->
                               let uu____1491 =
                                 let _0_330 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e, (FStar_Util.Inl t),
                                           (Some
                                              (c.FStar_Syntax_Syntax.lcomp_name)))))
                                     (Some (t.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env _0_330 c  in
                               (match uu____1491 with
                                | (e,c,f2) ->
                                    let _0_332 =
                                      let _0_331 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f
                                        _0_331
                                       in
                                    (e, c, _0_332))))))
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
           let uu____1596 = FStar_Syntax_Util.head_and_args top  in
           (match uu____1596 with
            | (unary_op,uu____1610) ->
                let head =
                  let _0_333 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (Prims.fst a).FStar_Syntax_Syntax.pos
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    _0_333
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
              FStar_Syntax_Syntax.tk = uu____1671;
              FStar_Syntax_Syntax.pos = uu____1672;
              FStar_Syntax_Syntax.vars = uu____1673;_},(e,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____1699 =
               let uu____1703 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               match uu____1703 with | (env0,uu____1711) -> tc_term env0 e
                in
             match uu____1699 with
             | (e,c,g) ->
                 let uu____1720 = FStar_Syntax_Util.head_and_args top  in
                 (match uu____1720 with
                  | (reify_op,uu____1734) ->
                      let repr = FStar_TypeChecker_Util.reify_comp env c  in
                      let e =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos
                         in
                      let c =
                        let _0_334 = FStar_Syntax_Syntax.mk_Total repr  in
                        FStar_All.pipe_right _0_334
                          (FStar_TypeChecker_Env.lcomp_of_comp env)
                         in
                      let uu____1771 = comp_check_expected_typ env e c  in
                      (match uu____1771 with
                       | (e,c,g') ->
                           let _0_335 = FStar_TypeChecker_Rel.conj_guard g g'
                              in
                           (e, c, _0_335)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____1782;
              FStar_Syntax_Syntax.pos = uu____1783;
              FStar_Syntax_Syntax.vars = uu____1784;_},(e,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____1816 =
               Prims.raise
                 (FStar_Errors.Error
                    (let _0_336 =
                       FStar_Util.format1 "Effect %s cannot be reified"
                         l.FStar_Ident.str
                        in
                     (_0_336, (e.FStar_Syntax_Syntax.pos))))
                in
             let uu____1820 = FStar_Syntax_Util.head_and_args top  in
             match uu____1820 with
             | (reflect_op,uu____1834) ->
                 let uu____1849 = FStar_TypeChecker_Env.effect_decl_opt env l
                    in
                 (match uu____1849 with
                  | None  -> no_reflect ()
                  | Some ed ->
                      let uu____1855 =
                        Prims.op_Negation
                          (FStar_All.pipe_right
                             ed.FStar_Syntax_Syntax.qualifiers
                             FStar_Syntax_Syntax.contains_reflectable)
                         in
                      if uu____1855
                      then no_reflect ()
                      else
                        (let uu____1861 =
                           FStar_TypeChecker_Env.clear_expected_typ env  in
                         match uu____1861 with
                         | (env_no_ex,topt) ->
                             let uu____1872 =
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
                                       (let _0_340 =
                                          let _0_339 =
                                            FStar_Syntax_Syntax.as_arg
                                              FStar_Syntax_Syntax.tun
                                             in
                                          let _0_338 =
                                            let _0_337 =
                                              FStar_Syntax_Syntax.as_arg
                                                FStar_Syntax_Syntax.tun
                                               in
                                            [_0_337]  in
                                          _0_339 :: _0_338  in
                                        (repr, _0_340)))) None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____1896 =
                                 let _0_342 =
                                   let _0_341 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env
                                      in
                                   FStar_All.pipe_right _0_341 Prims.fst  in
                                 tc_tot_or_gtot_term _0_342 t  in
                               match uu____1896 with
                               | (t,uu____1913,g) ->
                                   let uu____1915 =
                                     (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                      in
                                   (match uu____1915 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____1924,(res,uu____1926)::
                                         (wp,uu____1928)::[])
                                        -> (t, res, wp, g)
                                    | uu____1962 -> failwith "Impossible")
                                in
                             (match uu____1872 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____1986 =
                                    let uu____1989 =
                                      tc_tot_or_gtot_term env_no_ex e  in
                                    match uu____1989 with
                                    | (e,c,g) ->
                                        ((let uu____1999 =
                                            let _0_343 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation _0_343
                                             in
                                          if uu____1999
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env
                                              [("Expected Tot, got a GTot computation",
                                                 (e.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2005 =
                                            FStar_TypeChecker_Rel.try_teq
                                              env_no_ex
                                              c.FStar_Syntax_Syntax.lcomp_res_typ
                                              expected_repr_typ
                                             in
                                          match uu____2005 with
                                          | None  ->
                                              ((let _0_348 =
                                                  let _0_347 =
                                                    let _0_346 =
                                                      let _0_345 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let _0_344 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.lcomp_res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        _0_345 _0_344
                                                       in
                                                    (_0_346,
                                                      (e.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [_0_347]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env _0_348);
                                               (let _0_349 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e, _0_349)))
                                          | Some g' ->
                                              let _0_351 =
                                                let _0_350 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' _0_350
                                                 in
                                              (e, _0_351)))
                                     in
                                  (match uu____1986 with
                                   | (e,g) ->
                                       let c =
                                         let _0_358 =
                                           FStar_Syntax_Syntax.mk_Comp
                                             (let _0_357 =
                                                let _0_352 =
                                                  env.FStar_TypeChecker_Env.universe_of
                                                    env res_typ
                                                   in
                                                [_0_352]  in
                                              let _0_356 =
                                                let _0_355 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    res_typ
                                                   in
                                                let _0_354 =
                                                  let _0_353 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [_0_353]  in
                                                _0_355 :: _0_354  in
                                              {
                                                FStar_Syntax_Syntax.comp_typ_name
                                                  =
                                                  (ed.FStar_Syntax_Syntax.mname);
                                                FStar_Syntax_Syntax.comp_univs
                                                  = _0_357;
                                                FStar_Syntax_Syntax.effect_args
                                                  = _0_356;
                                                FStar_Syntax_Syntax.flags =
                                                  []
                                              })
                                            in
                                         FStar_All.pipe_right _0_358
                                           (FStar_TypeChecker_Env.lcomp_of_comp
                                              env)
                                          in
                                       let e =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____2041 =
                                         comp_check_expected_typ env e c  in
                                       (match uu____2041 with
                                        | (e,c,g') ->
                                            let _0_359 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e, c, _0_359))))))))
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let env0 = env  in
           let env =
             let _0_361 =
               let _0_360 = FStar_TypeChecker_Env.clear_expected_typ env  in
               FStar_All.pipe_right _0_360 Prims.fst  in
             FStar_All.pipe_right _0_361 instantiate_both  in
           ((let uu____2074 =
               FStar_TypeChecker_Env.debug env FStar_Options.High  in
             if uu____2074
             then
               let _0_363 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let _0_362 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" _0_363 _0_362
             else ());
            (let uu____2076 = tc_term (no_inst env) head  in
             match uu____2076 with
             | (head,chead,g_head) ->
                 let uu____2086 =
                   let uu____2090 =
                     (Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head)
                      in
                   if uu____2090
                   then
                     let _0_364 = FStar_TypeChecker_Env.expected_typ env0  in
                     check_short_circuit_args env head chead g_head args
                       _0_364
                   else
                     (let _0_365 = FStar_TypeChecker_Env.expected_typ env0
                         in
                      check_application_args env head chead g_head args
                        _0_365)
                    in
                 (match uu____2086 with
                  | (e,c,g) ->
                      ((let uu____2102 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Extreme
                           in
                        if uu____2102
                        then
                          let _0_366 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            _0_366
                        else ());
                       (let c =
                          let uu____2105 =
                            ((FStar_TypeChecker_Env.should_verify env) &&
                               (Prims.op_Negation
                                  (FStar_Syntax_Util.is_lcomp_partial_return
                                     c)))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                             in
                          if uu____2105
                          then
                            FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                              env e c
                          else c  in
                        let uu____2107 = comp_check_expected_typ env0 e c  in
                        match uu____2107 with
                        | (e,c,g') ->
                            let gimp =
                              let uu____2118 =
                                (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                                 in
                              match uu____2118 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2120) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e,
                                      (c.FStar_Syntax_Syntax.lcomp_res_typ),
                                      (head.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___90_2152 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___90_2152.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___90_2152.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___90_2152.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2177 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let _0_367 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g _0_367  in
                            ((let uu____2180 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____2180
                              then
                                let _0_369 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let _0_368 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  _0_369 _0_368
                              else ());
                             (e, c, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2210 = FStar_TypeChecker_Env.clear_expected_typ env  in
           (match uu____2210 with
            | (env1,topt) ->
                let env1 = instantiate_both env1  in
                let uu____2222 = tc_term env1 e1  in
                (match uu____2222 with
                 | (e1,c1,g1) ->
                     let uu____2232 =
                       match topt with
                       | Some t -> (env, t)
                       | None  ->
                           let uu____2238 = FStar_Syntax_Util.type_u ()  in
                           (match uu____2238 with
                            | (k,uu____2244) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env k  in
                                let _0_370 =
                                  FStar_TypeChecker_Env.set_expected_typ env
                                    res_t
                                   in
                                (_0_370, res_t))
                        in
                     (match uu____2232 with
                      | (env_branches,res_t) ->
                          ((let uu____2252 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____2252
                            then
                              let _0_371 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                _0_371
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e1.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.lcomp_res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____2303 =
                              let uu____2306 =
                                FStar_List.fold_right
                                  (fun uu____2325  ->
                                     fun uu____2326  ->
                                       match (uu____2325, uu____2326) with
                                       | ((uu____2358,f,c,g),(caccum,gaccum))
                                           ->
                                           let _0_372 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), _0_372))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____2306 with
                              | (cases,g) ->
                                  let _0_373 =
                                    FStar_TypeChecker_Util.bind_cases env
                                      res_t cases
                                     in
                                  (_0_373, g)
                               in
                            match uu____2303 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind env (Some e1)
                                    c1 ((Some guard_x), c_branches)
                                   in
                                let e =
                                  let mk_match scrutinee =
                                    let scrutinee =
                                      FStar_TypeChecker_Util.maybe_lift env
                                        scrutinee
                                        c1.FStar_Syntax_Syntax.lcomp_name
                                        cres.FStar_Syntax_Syntax.lcomp_name
                                        c1.FStar_Syntax_Syntax.lcomp_res_typ
                                       in
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____2460  ->
                                              match uu____2460 with
                                              | ((pat,wopt,br),uu____2476,lc,uu____2478)
                                                  ->
                                                  let _0_374 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env br
                                                      lc.FStar_Syntax_Syntax.lcomp_name
                                                      cres.FStar_Syntax_Syntax.lcomp_name
                                                      lc.FStar_Syntax_Syntax.lcomp_res_typ
                                                     in
                                                  (pat, wopt, _0_374)))
                                       in
                                    let e =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_match
                                            (scrutinee, branches)))
                                        (Some
                                           ((cres.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    (FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_ascribed
                                          (e,
                                            (FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.lcomp_res_typ)),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.lcomp_name)))))
                                      None e.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____2523 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env c1.FStar_Syntax_Syntax.lcomp_name
                                     in
                                  if uu____2523
                                  then mk_match e1
                                  else
                                    (let e_match =
                                       mk_match
                                         (FStar_Syntax_Syntax.bv_to_name
                                            guard_x)
                                        in
                                     let lb =
                                       let _0_375 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env
                                           c1.FStar_Syntax_Syntax.lcomp_name
                                          in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (FStar_Util.Inl guard_x);
                                         FStar_Syntax_Syntax.lbunivs = [];
                                         FStar_Syntax_Syntax.lbtyp =
                                           (c1.FStar_Syntax_Syntax.lcomp_res_typ);
                                         FStar_Syntax_Syntax.lbeff = _0_375;
                                         FStar_Syntax_Syntax.lbdef = e1
                                       }  in
                                     let e =
                                       (FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_let
                                             (let _0_378 =
                                                let _0_377 =
                                                  let _0_376 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      guard_x
                                                     in
                                                  [_0_376]  in
                                                FStar_Syntax_Subst.close
                                                  _0_377 e_match
                                                 in
                                              ((false, [lb]), _0_378))))
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic env
                                       e cres.FStar_Syntax_Syntax.lcomp_name
                                       cres.FStar_Syntax_Syntax.lcomp_res_typ)
                                   in
                                ((let uu____2547 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____2547
                                  then
                                    let _0_381 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let _0_380 =
                                      let _0_379 =
                                        cres.FStar_Syntax_Syntax.lcomp_as_comp
                                          ()
                                         in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        _0_379
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      _0_381 _0_380
                                  else ());
                                 (let _0_382 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e, cres, _0_382))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2551;
                FStar_Syntax_Syntax.lbunivs = uu____2552;
                FStar_Syntax_Syntax.lbtyp = uu____2553;
                FStar_Syntax_Syntax.lbeff = uu____2554;
                FStar_Syntax_Syntax.lbdef = uu____2555;_}::[]),uu____2556)
           ->
           ((let uu____2571 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             if uu____2571
             then
               let _0_383 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" _0_383
             else ());
            check_top_level_let env top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2573),uu____2574) ->
           check_inner_let env top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2584;
                FStar_Syntax_Syntax.lbunivs = uu____2585;
                FStar_Syntax_Syntax.lbtyp = uu____2586;
                FStar_Syntax_Syntax.lbeff = uu____2587;
                FStar_Syntax_Syntax.lbdef = uu____2588;_}::uu____2589),uu____2590)
           ->
           ((let uu____2606 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             if uu____2606
             then
               let _0_384 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" _0_384
             else ());
            check_top_level_let_rec env top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____2608),uu____2609) ->
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
        let uu____2653 = FStar_TypeChecker_Util.maybe_instantiate env e t  in
        match uu____2653 with
        | (e,t,implicits,_subst) ->
            let tc =
              let uu____2668 = FStar_TypeChecker_Env.should_verify env  in
              if uu____2668
              then FStar_Util.Inl t
              else
                FStar_Util.Inr
                  ((let _0_385 = FStar_Syntax_Syntax.mk_Total t  in
                    FStar_TypeChecker_Env.lcomp_of_comp env _0_385))
               in
            let is_data_ctor uu___79_2676 =
              match uu___79_2676 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____2679 -> false  in
            let uu____2681 =
              (is_data_ctor dc) &&
                (Prims.op_Negation
                   (FStar_TypeChecker_Env.is_datacon env
                      v.FStar_Syntax_Syntax.v))
               in
            if uu____2681
            then
              Prims.raise
                (FStar_Errors.Error
                   (let _0_387 =
                      FStar_Util.format1
                        "Expected a data constructor; got %s"
                        (v.FStar_Syntax_Syntax.v).FStar_Ident.str
                       in
                    let _0_386 = FStar_TypeChecker_Env.get_range env  in
                    (_0_387, _0_386)))
            else value_check_expected_typ env e tc implicits
         in
      let env = FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          failwith
            (let _0_388 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format1
               "Impossible: Violation of locally nameless convention: %s"
               _0_388)
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____2717 =
              (FStar_Syntax_Subst.compress t1).FStar_Syntax_Syntax.n  in
            match uu____2717 with
            | FStar_Syntax_Syntax.Tm_arrow uu____2718 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____2726 ->
                let imp =
                  ("uvar in term", env, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___91_2746 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___91_2746.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___91_2746.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___91_2746.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env  in
          let uu____2774 =
            let uu____2781 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____2781 with
            | None  ->
                let uu____2789 = FStar_Syntax_Util.type_u ()  in
                (match uu____2789 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard)  in
          (match uu____2774 with
           | (t,uu____2810,g0) ->
               let uu____2818 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env t
                  in
               (match uu____2818 with
                | (e,uu____2829,g1) ->
                    let _0_391 =
                      let _0_389 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right _0_389
                        (FStar_TypeChecker_Env.lcomp_of_comp env)
                       in
                    let _0_390 = FStar_TypeChecker_Rel.conj_guard g0 g1  in
                    (e, _0_391, _0_390)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let t =
            if env.FStar_TypeChecker_Env.use_bv_sorts
            then x.FStar_Syntax_Syntax.sort
            else FStar_TypeChecker_Env.lookup_bv env x  in
          let x =
            let uu___92_2845 = x  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___92_2845.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___92_2845.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = t
            }  in
          (FStar_TypeChecker_Common.insert_bv x t;
           (let e = FStar_Syntax_Syntax.bv_to_name x  in
            let uu____2848 = FStar_TypeChecker_Util.maybe_instantiate env e t
               in
            match uu____2848 with
            | (e,t,implicits,_subst) ->
                let tc =
                  let uu____2863 = FStar_TypeChecker_Env.should_verify env
                     in
                  if uu____2863
                  then FStar_Util.Inl t
                  else
                    FStar_Util.Inr
                      ((let _0_392 = FStar_Syntax_Syntax.mk_Total t  in
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.lcomp_of_comp env) _0_392))
                   in
                value_check_expected_typ env e tc implicits))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____2868;
             FStar_Syntax_Syntax.pos = uu____2869;
             FStar_Syntax_Syntax.vars = uu____2870;_},us)
          ->
          let us = FStar_List.map (tc_universe env) us  in
          let uu____2878 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____2878 with
           | (us',t) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_393 = FStar_TypeChecker_Env.get_range env  in
                        ("Unexpected number of universe instantiations",
                          _0_393)))
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____2902 -> failwith "Impossible") us' us;
                (let fv' =
                   let uu___93_2904 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___94_2905 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___94_2905.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___94_2905.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___93_2904.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___93_2904.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e =
                    let _0_394 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst _0_394 us  in
                  check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2939 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____2939 with
           | (us,t) ->
               ((let uu____2952 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Range")
                    in
                 if uu____2952
                 then
                   let _0_399 =
                     FStar_Syntax_Print.lid_to_string
                       (FStar_Syntax_Syntax.lid_of_fv fv)
                      in
                   let _0_398 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let _0_397 =
                     FStar_Range.string_of_range
                       (FStar_Ident.range_of_lid
                          (FStar_Syntax_Syntax.lid_of_fv fv))
                      in
                   let _0_396 =
                     FStar_Range.string_of_use_range
                       (FStar_Ident.range_of_lid
                          (FStar_Syntax_Syntax.lid_of_fv fv))
                      in
                   let _0_395 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s"
                     _0_399 _0_398 _0_397 _0_396 _0_395
                 else ());
                (let fv' =
                   let uu___95_2955 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___96_2956 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___96_2956.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___96_2956.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___95_2955.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___95_2955.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 FStar_TypeChecker_Common.insert_fv fv t;
                 (let e =
                    let _0_400 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst _0_400 us  in
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
          let uu____3014 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3014 with
           | (bs,c) ->
               let env0 = env  in
               let uu____3023 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____3023 with
                | (env,uu____3031) ->
                    let uu____3034 = tc_binders env bs  in
                    (match uu____3034 with
                     | (bs,env,g,us) ->
                         let uu____3046 = tc_comp env c  in
                         (match uu____3046 with
                          | (c,uc,f) ->
                              let e =
                                let uu___97_3059 =
                                  FStar_Syntax_Util.arrow bs c  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___97_3059.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___97_3059.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___97_3059.FStar_Syntax_Syntax.vars)
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
                                  let _0_401 =
                                    FStar_TypeChecker_Rel.close_guard bs f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g _0_401
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
          let uu____3112 =
            let _0_403 =
              let _0_402 = FStar_Syntax_Syntax.mk_binder x  in [_0_402]  in
            FStar_Syntax_Subst.open_term _0_403 phi  in
          (match uu____3112 with
           | (x,phi) ->
               let env0 = env  in
               let uu____3121 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____3121 with
                | (env,uu____3129) ->
                    let uu____3132 =
                      let _0_404 = FStar_List.hd x  in tc_binder env _0_404
                       in
                    (match uu____3132 with
                     | (x,env,f1,u) ->
                         ((let uu____3153 =
                             FStar_TypeChecker_Env.debug env
                               FStar_Options.High
                              in
                           if uu____3153
                           then
                             let _0_407 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let _0_406 =
                               FStar_Syntax_Print.term_to_string phi  in
                             let _0_405 =
                               FStar_Syntax_Print.bv_to_string (Prims.fst x)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               _0_407 _0_406 _0_405
                           else ());
                          (let uu____3155 = FStar_Syntax_Util.type_u ()  in
                           match uu____3155 with
                           | (t_phi,uu____3162) ->
                               let uu____3163 =
                                 tc_check_tot_or_gtot_term env phi t_phi  in
                               (match uu____3163 with
                                | (phi,uu____3171,f2) ->
                                    let e =
                                      let uu___98_3176 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x) phi
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___98_3176.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___98_3176.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___98_3176.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let _0_408 =
                                        FStar_TypeChecker_Rel.close_guard 
                                          [x] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        _0_408
                                       in
                                    value_check_expected_typ env0 e
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3203) ->
          let bs = FStar_TypeChecker_Util.maybe_add_implicit_binders env bs
             in
          ((let uu____3228 =
              FStar_TypeChecker_Env.debug env FStar_Options.Low  in
            if uu____3228
            then
              let _0_409 =
                FStar_Syntax_Print.term_to_string
                  (let uu___99_3229 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___99_3229.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___99_3229.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___99_3229.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" _0_409
            else ());
           (let uu____3248 = FStar_Syntax_Subst.open_term bs body  in
            match uu____3248 with | (bs,body) -> tc_abs env top bs body))
      | uu____3256 ->
          failwith
            (let _0_411 = FStar_Syntax_Print.term_to_string top  in
             let _0_410 = FStar_Syntax_Print.tag_of_term top  in
             FStar_Util.format2 "Unexpected value: %s (%s)" _0_411 _0_410)

and tc_constant :
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3262 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3263,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3269,Some uu____3270) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3278 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3282 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3283 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3284 ->
          FStar_TypeChecker_Common.t_range
      | uu____3285 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____3296) ->
          let uu____3303 = FStar_Syntax_Util.type_u ()  in
          (match uu____3303 with
           | (k,u) ->
               let uu____3311 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3311 with
                | (t,uu____3319,g) ->
                    let _0_412 = FStar_Syntax_Syntax.mk_Total' t (Some u)  in
                    (_0_412, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3322) ->
          let uu____3329 = FStar_Syntax_Util.type_u ()  in
          (match uu____3329 with
           | (k,u) ->
               let uu____3337 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3337 with
                | (t,uu____3345,g) ->
                    let _0_413 = FStar_Syntax_Syntax.mk_GTotal' t (Some u)
                       in
                    (_0_413, u, g)))
      | FStar_Syntax_Syntax.Comp c ->
          let head =
            FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.comp_typ_name
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
            (FStar_Syntax_Syntax.mk_Tm_app head
               c.FStar_Syntax_Syntax.effect_args) None
              c0.FStar_Syntax_Syntax.pos
             in
          let uu____3366 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____3366 with
           | (tc,uu____3374,f) ->
               let uu____3376 = FStar_Syntax_Util.head_and_args tc  in
               (match uu____3376 with
                | (head,args) ->
                    let comp_univs =
                      let uu____3406 =
                        (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                         in
                      match uu____3406 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3407,us) -> us
                      | uu____3413 -> []  in
                    let uu____3414 = FStar_Syntax_Util.head_and_args tc  in
                    (match uu____3414 with
                     | (uu____3427,args) ->
                         let uu____3443 =
                           let _0_414 =
                             FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                               (FStar_List.map
                                  (fun uu___80_3461  ->
                                     match uu___80_3461 with
                                     | FStar_Syntax_Syntax.DECREASES e ->
                                         let uu____3467 =
                                           FStar_TypeChecker_Env.clear_expected_typ
                                             env
                                            in
                                         (match uu____3467 with
                                          | (env,uu____3474) ->
                                              let uu____3477 =
                                                tc_tot_or_gtot_term env e  in
                                              (match uu____3477 with
                                               | (e,uu____3484,g) ->
                                                   ((FStar_Syntax_Syntax.DECREASES
                                                       e), g)))
                                     | f ->
                                         (f,
                                           FStar_TypeChecker_Rel.trivial_guard)))
                              in
                           FStar_All.pipe_right _0_414 FStar_List.unzip  in
                         (match uu____3443 with
                          | (flags,guards) ->
                              let c =
                                FStar_Syntax_Syntax.mk_Comp
                                  (let uu___100_3497 = c  in
                                   {
                                     FStar_Syntax_Syntax.comp_typ_name =
                                       (uu___100_3497.FStar_Syntax_Syntax.comp_typ_name);
                                     FStar_Syntax_Syntax.comp_univs =
                                       comp_univs;
                                     FStar_Syntax_Syntax.effect_args = args;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___100_3497.FStar_Syntax_Syntax.flags)
                                   })
                                 in
                              let u_c =
                                let uu____3499 =
                                  FStar_TypeChecker_Util.effect_repr env c
                                   in
                                match uu____3499 with
                                | None  ->
                                    let _0_415 =
                                      Prims.fst
                                        (FStar_TypeChecker_Env.comp_as_normal_comp_typ
                                           env c).FStar_TypeChecker_Env.nct_result
                                       in
                                    env.FStar_TypeChecker_Env.universe_of env
                                      _0_415
                                | Some tm ->
                                    env.FStar_TypeChecker_Env.universe_of env
                                      tm
                                 in
                              let _0_416 =
                                FStar_List.fold_left
                                  FStar_TypeChecker_Rel.conj_guard f guards
                                 in
                              (c, u_c, _0_416)))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u =
        let u = FStar_Syntax_Subst.compress_univ u  in
        match u with
        | FStar_Syntax_Syntax.U_bvar uu____3511 ->
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
             let _0_417 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right _0_417 Prims.snd
         | uu____3520 -> aux u)

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
                 (let _0_418 =
                    FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                      env msg t top
                     in
                  (_0_418, (top.FStar_Syntax_Syntax.pos))))
             in
          let check_binders env bs bs_expected =
            let rec aux uu____3594 bs bs_expected =
              match uu____3594 with
              | (env,out,g,subst) ->
                  (match (bs, bs_expected) with
                   | ([],[]) -> (env, (FStar_List.rev out), None, g, subst)
                   | ((hd,imp)::bs,(hd_expected,imp')::bs_expected) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             Prims.raise
                               (FStar_Errors.Error
                                  (let _0_421 =
                                     let _0_419 =
                                       FStar_Syntax_Print.bv_to_string hd  in
                                     FStar_Util.format1
                                       "Inconsistent implicit argument annotation on argument %s"
                                       _0_419
                                      in
                                   let _0_420 =
                                     FStar_Syntax_Syntax.range_of_bv hd  in
                                   (_0_421, _0_420)))
                         | uu____3691 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____3695 =
                           let uu____3698 =
                             (FStar_Syntax_Util.unmeta
                                hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              in
                           match uu____3698 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____3701 ->
                               ((let uu____3703 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.High
                                    in
                                 if uu____3703
                                 then
                                   let _0_422 =
                                     FStar_Syntax_Print.bv_to_string hd  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     _0_422
                                 else ());
                                (let uu____3705 =
                                   tc_tot_or_gtot_term env
                                     hd.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____3705 with
                                 | (t,uu____3712,g1) ->
                                     let g2 =
                                       let _0_424 =
                                         FStar_TypeChecker_Env.get_range env
                                          in
                                       let _0_423 =
                                         FStar_TypeChecker_Rel.teq env t
                                           expected_t
                                          in
                                       FStar_TypeChecker_Util.label_guard
                                         _0_424
                                         "Type annotation on parameter incompatible with the expected type"
                                         _0_423
                                        in
                                     let g =
                                       let _0_425 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         _0_425
                                        in
                                     (t, g)))
                            in
                         match uu____3695 with
                         | (t,g) ->
                             let hd =
                               let uu___101_3731 = hd  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___101_3731.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___101_3731.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env = push_binding env b  in
                             let subst =
                               let _0_426 = FStar_Syntax_Syntax.bv_to_name hd
                                  in
                               maybe_extend_subst subst b_expected _0_426  in
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
                  | uu____3833 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____3837 = tc_binders env bs  in
                  match uu____3837 with
                  | (bs,envbody,g,uu____3856) ->
                      let uu____3857 =
                        let uu____3862 =
                          (FStar_Syntax_Subst.compress body).FStar_Syntax_Syntax.n
                           in
                        match uu____3862 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,FStar_Util.Inr c,uu____3869) ->
                            let uu____3888 = tc_comp envbody c  in
                            (match uu____3888 with
                             | (c,uu____3897,g') ->
                                 let _0_427 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((Some c), body, _0_427))
                        | uu____3900 -> (None, body, g)  in
                      (match uu____3857 with
                       | (copt,body,g) ->
                           (None, bs, [], copt, envbody, body, g))))
            | Some t ->
                let t = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm t =
                  let uu____3950 =
                    (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
                  match uu____3950 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____3979 -> failwith "Impossible");
                       (let uu____3983 = tc_binders env bs  in
                        match uu____3983 with
                        | (bs,envbody,g,uu____4003) ->
                            let uu____4004 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____4004 with
                             | (envbody,uu____4021) ->
                                 ((Some (t, true)), bs, [], None, envbody,
                                   body, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4032) ->
                      let uu____4037 =
                        as_function_typ norm b.FStar_Syntax_Syntax.sort  in
                      (match uu____4037 with
                       | (uu____4062,bs,bs',copt,env,body,g) ->
                           ((Some (t, false)), bs, bs', copt, env, body, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4098 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____4098 with
                       | (bs_expected,c_expected) ->
                           let check_actuals_against_formals env bs
                             bs_expected =
                             let rec handle_more uu____4156 c_expected =
                               match uu____4156 with
                               | (env,bs,more,guard,subst) ->
                                   (match more with
                                    | None  ->
                                        let _0_428 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected
                                           in
                                        (env, bs, guard, _0_428)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          FStar_Syntax_Syntax.mk_Total
                                            (FStar_Syntax_Util.arrow
                                               more_bs_expected c_expected)
                                           in
                                        let _0_429 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c
                                           in
                                        (env, bs, guard, _0_429)
                                    | Some (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected
                                           in
                                        if FStar_Syntax_Util.is_named_tot c
                                        then
                                          let t =
                                            let _0_430 =
                                              FStar_TypeChecker_Env.result_typ
                                                env c
                                               in
                                            unfold_whnf env _0_430  in
                                          (match t.FStar_Syntax_Syntax.n with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected,c_expected) ->
                                               let uu____4246 =
                                                 check_binders env more_bs
                                                   bs_expected
                                                  in
                                               (match uu____4246 with
                                                | (env,bs',more,guard',subst)
                                                    ->
                                                    let _0_432 =
                                                      let _0_431 =
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          guard guard'
                                                         in
                                                      (env,
                                                        (FStar_List.append bs
                                                           bs'), more,
                                                        _0_431, subst)
                                                       in
                                                    handle_more _0_432
                                                      c_expected)
                                           | uu____4281 ->
                                               let _0_434 =
                                                 let _0_433 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t
                                                    in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   _0_433
                                                  in
                                               fail _0_434 t)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t)
                                in
                             let _0_435 = check_binders env bs bs_expected
                                in
                             handle_more _0_435 c_expected  in
                           let mk_letrec_env envbody bs c =
                             let letrecs = guard_letrecs envbody bs c  in
                             let envbody =
                               let uu___102_4319 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___102_4319.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___102_4319.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___102_4319.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___102_4319.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___102_4319.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___102_4319.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___102_4319.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___102_4319.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___102_4319.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___102_4319.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___102_4319.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___102_4319.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___102_4319.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___102_4319.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___102_4319.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___102_4319.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___102_4319.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___102_4319.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___102_4319.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___102_4319.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___102_4319.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___102_4319.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___102_4319.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____4333  ->
                                     fun uu____4334  ->
                                       match (uu____4333, uu____4334) with
                                       | ((env,letrec_binders),(l,t)) ->
                                           let uu____4359 =
                                             let _0_437 =
                                               let _0_436 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env
                                                  in
                                               FStar_All.pipe_right _0_436
                                                 Prims.fst
                                                in
                                             tc_term _0_437 t  in
                                           (match uu____4359 with
                                            | (t,uu____4371,uu____4372) ->
                                                let env =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env l ([], t)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let _0_438 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___103_4379
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___103_4379.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___103_4379.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t
                                                           })
                                                         in
                                                      _0_438 ::
                                                        letrec_binders
                                                  | uu____4380 ->
                                                      letrec_binders
                                                   in
                                                (env, lb))) (envbody, []))
                              in
                           let uu____4383 =
                             check_actuals_against_formals env bs bs_expected
                              in
                           (match uu____4383 with
                            | (envbody,bs,g,c) ->
                                let uu____4413 =
                                  let uu____4417 =
                                    FStar_TypeChecker_Env.should_verify env
                                     in
                                  if uu____4417
                                  then mk_letrec_env envbody bs c
                                  else (envbody, [])  in
                                (match uu____4413 with
                                 | (envbody,letrecs) ->
                                     let envbody =
                                       let _0_439 =
                                         FStar_TypeChecker_Env.result_typ env
                                           c
                                          in
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody _0_439
                                        in
                                     ((Some (t, false)), bs, letrecs,
                                       (Some c), envbody, body, g))))
                  | uu____4450 ->
                      if Prims.op_Negation norm
                      then
                        let _0_440 = unfold_whnf env t  in
                        as_function_typ true _0_440
                      else
                        (let uu____4464 = expected_function_typ env None body
                            in
                         match uu____4464 with
                         | (uu____4488,bs,uu____4490,c_opt,envbody,body,g) ->
                             ((Some (t, false)), bs, [], c_opt, envbody,
                               body, g))
                   in
                as_function_typ false t
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____4511 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____4511 with
          | (env,topt) ->
              ((let uu____4523 =
                  FStar_TypeChecker_Env.debug env FStar_Options.High  in
                if uu____4523
                then
                  let _0_441 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    _0_441
                    (if env.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____4527 = expected_function_typ env topt body  in
                match uu____4527 with
                | (tfun_opt,bs,letrec_binders,c_opt,envbody,body,g) ->
                    let uu____4557 =
                      tc_term
                        (let uu___104_4561 = envbody  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___104_4561.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___104_4561.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___104_4561.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___104_4561.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___104_4561.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___104_4561.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___104_4561.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___104_4561.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___104_4561.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___104_4561.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___104_4561.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___104_4561.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___104_4561.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___104_4561.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___104_4561.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___104_4561.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___104_4561.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___104_4561.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___104_4561.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___104_4561.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___104_4561.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___104_4561.FStar_TypeChecker_Env.qname_and_index)
                         }) body
                       in
                    (match uu____4557 with
                     | (body,cbody,guard_body) ->
                         let guard_body =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         ((let uu____4570 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Implicits")
                              in
                           if uu____4570
                           then
                             let _0_444 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body.FStar_TypeChecker_Env.implicits)
                                in
                             let _0_443 =
                               let _0_442 =
                                 cbody.FStar_Syntax_Syntax.lcomp_as_comp ()
                                  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string _0_442
                                in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               _0_444 _0_443
                           else ());
                          (let uu____4580 =
                             let _0_446 =
                               let _0_445 =
                                 cbody.FStar_Syntax_Syntax.lcomp_as_comp ()
                                  in
                               (body, _0_445)  in
                             check_expected_effect
                               (let uu___105_4584 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___105_4584.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___105_4584.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___105_4584.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___105_4584.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___105_4584.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___105_4584.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___105_4584.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___105_4584.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___105_4584.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___105_4584.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___105_4584.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___105_4584.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___105_4584.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___105_4584.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___105_4584.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___105_4584.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___105_4584.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___105_4584.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___105_4584.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___105_4584.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___105_4584.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___105_4584.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___105_4584.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt _0_446
                              in
                           match uu____4580 with
                           | (body,cbody,guard) ->
                               let guard =
                                 FStar_TypeChecker_Rel.conj_guard guard_body
                                   guard
                                  in
                               let guard =
                                 let uu____4595 =
                                   env.FStar_TypeChecker_Env.top_level ||
                                     (Prims.op_Negation
                                        (FStar_TypeChecker_Env.should_verify
                                           env))
                                    in
                                 if uu____4595
                                 then
                                   let _0_447 =
                                     FStar_TypeChecker_Rel.conj_guard g guard
                                      in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody _0_447
                                 else
                                   (let guard =
                                      let _0_448 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard
                                         in
                                      FStar_TypeChecker_Rel.close_guard
                                        (FStar_List.append bs letrec_binders)
                                        _0_448
                                       in
                                    guard)
                                  in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs cbody  in
                               let e =
                                 let _0_449 =
                                   Some
                                     (FStar_Util.Inl
                                        (FStar_TypeChecker_Env.lcomp_of_comp
                                           env (FStar_Util.dflt cbody c_opt)))
                                    in
                                 FStar_Syntax_Util.abs bs body _0_449  in
                               let uu____4610 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t = FStar_Syntax_Subst.compress t
                                        in
                                     (match t.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____4625 -> (e, t, guard)
                                      | uu____4633 ->
                                          let uu____4634 =
                                            if use_teq
                                            then
                                              let _0_450 =
                                                FStar_TypeChecker_Rel.teq env
                                                  t tfun_computed
                                                 in
                                              (e, _0_450)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env e tfun_computed t
                                             in
                                          (match uu____4634 with
                                           | (e,guard') ->
                                               let _0_451 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard guard'
                                                  in
                                               (e, t, _0_451)))
                                 | None  -> (e, tfun_computed, guard)  in
                               (match uu____4610 with
                                | (e,tfun,guard) ->
                                    let c =
                                      if env.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env tfun e
                                       in
                                    let uu____4655 =
                                      let _0_452 =
                                        FStar_TypeChecker_Env.lcomp_of_comp
                                          env c
                                         in
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env e _0_452 guard
                                       in
                                    (match uu____4655 with
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
              let thead = chead.FStar_Syntax_Syntax.lcomp_res_typ  in
              (let uu____4691 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____4691
               then
                 let _0_454 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos
                    in
                 let _0_453 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" _0_454 _0_453
               else ());
              (let monadic_application uu____4734 subst arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____4734 with
                 | (head,chead,ghead,cres) ->
                     let rt =
                       check_no_escape (Some head) env fvs
                         cres.FStar_Syntax_Syntax.lcomp_res_typ
                        in
                     let cres =
                       let uu___106_4776 = cres  in
                       {
                         FStar_Syntax_Syntax.lcomp_name =
                           (uu___106_4776.FStar_Syntax_Syntax.lcomp_name);
                         FStar_Syntax_Syntax.lcomp_univs =
                           (uu___106_4776.FStar_Syntax_Syntax.lcomp_univs);
                         FStar_Syntax_Syntax.lcomp_indices =
                           (uu___106_4776.FStar_Syntax_Syntax.lcomp_indices);
                         FStar_Syntax_Syntax.lcomp_res_typ = rt;
                         FStar_Syntax_Syntax.lcomp_cflags =
                           (uu___106_4776.FStar_Syntax_Syntax.lcomp_cflags);
                         FStar_Syntax_Syntax.lcomp_as_comp =
                           (uu___106_4776.FStar_Syntax_Syntax.lcomp_as_comp)
                       }  in
                     let uu____4777 =
                       match bs with
                       | [] ->
                           let cres =
                             FStar_Syntax_Subst.subst_lcomp subst cres  in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead guard  in
                           let refine_with_equality =
                             (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres)
                               &&
                               (FStar_All.pipe_right arg_comps_rev
                                  (FStar_Util.for_some
                                     (fun uu___81_4804  ->
                                        match uu___81_4804 with
                                        | (uu____4813,uu____4814,FStar_Util.Inl
                                           uu____4815) -> false
                                        | (uu____4826,uu____4827,FStar_Util.Inr
                                           c) ->
                                            Prims.op_Negation
                                              (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 c))))
                              in
                           let cres =
                             if refine_with_equality
                             then
                               let _0_455 =
                                 (FStar_Syntax_Syntax.mk_Tm_app head
                                    (FStar_List.rev arg_rets))
                                   (Some
                                      ((cres.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                   r
                                  in
                               FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                 env _0_455 cres
                             else
                               ((let uu____4850 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____4850
                                 then
                                   let _0_458 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let _0_457 =
                                     FStar_Syntax_Print.lcomp_to_string cres
                                      in
                                   let _0_456 =
                                     FStar_TypeChecker_Rel.guard_to_string
                                       env g
                                      in
                                   FStar_Util.print3
                                     "Not refining result: f=%s; cres=%s; guard=%s\n"
                                     _0_458 _0_457 _0_456
                                 else ());
                                cres)
                              in
                           (cres, g)
                       | uu____4852 ->
                           let g =
                             let _0_459 =
                               FStar_TypeChecker_Rel.conj_guard ghead guard
                                in
                             FStar_All.pipe_right _0_459
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let _0_463 =
                             let _0_462 =
                               FStar_Syntax_Syntax.mk_Total
                                 (let _0_461 =
                                    let _0_460 =
                                      cres.FStar_Syntax_Syntax.lcomp_as_comp
                                        ()
                                       in
                                    FStar_Syntax_Util.arrow bs _0_460  in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.subst subst) _0_461)
                                in
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.lcomp_of_comp env)
                               _0_462
                              in
                           (_0_463, g)
                        in
                     (match uu____4777 with
                      | (cres,guard) ->
                          ((let uu____4863 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____4863
                            then
                              let _0_464 =
                                FStar_Syntax_Print.lcomp_to_string cres  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" _0_464
                            else ());
                           (let uu____4865 =
                              FStar_List.fold_left
                                (fun uu____4888  ->
                                   fun uu____4889  ->
                                     match (uu____4888, uu____4889) with
                                     | ((args,out_c,monadic),((e,q),x,c)) ->
                                         (match c with
                                          | FStar_Util.Inl (eff_name,arg_typ)
                                              ->
                                              let _0_467 =
                                                let _0_466 =
                                                  let _0_465 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env e eff_name
                                                      out_c.FStar_Syntax_Syntax.lcomp_name
                                                      arg_typ
                                                     in
                                                  (_0_465, q)  in
                                                _0_466 :: args  in
                                              (_0_467, out_c, monadic)
                                          | FStar_Util.Inr c ->
                                              let monadic =
                                                monadic ||
                                                  (Prims.op_Negation
                                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                        c))
                                                 in
                                              let out_c =
                                                FStar_TypeChecker_Util.bind
                                                  env None c (x, out_c)
                                                 in
                                              let e =
                                                FStar_TypeChecker_Util.maybe_monadic
                                                  env e
                                                  c.FStar_Syntax_Syntax.lcomp_name
                                                  c.FStar_Syntax_Syntax.lcomp_res_typ
                                                 in
                                              let e =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env e
                                                  c.FStar_Syntax_Syntax.lcomp_name
                                                  out_c.FStar_Syntax_Syntax.lcomp_name
                                                  c.FStar_Syntax_Syntax.lcomp_res_typ
                                                 in
                                              (((e, q) :: args), out_c,
                                                monadic))) ([], cres, false)
                                arg_comps_rev
                               in
                            match uu____4865 with
                            | (args,comp,monadic) ->
                                let comp =
                                  FStar_TypeChecker_Util.bind env None chead
                                    (None, comp)
                                   in
                                let app =
                                  (FStar_Syntax_Syntax.mk_Tm_app head args)
                                    (Some
                                       ((comp.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                    r
                                   in
                                let app =
                                  let uu____5024 =
                                    monadic ||
                                      (Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                            comp))
                                     in
                                  if uu____5024
                                  then
                                    FStar_TypeChecker_Util.maybe_monadic env
                                      app comp.FStar_Syntax_Syntax.lcomp_name
                                      comp.FStar_Syntax_Syntax.lcomp_res_typ
                                  else app  in
                                let uu____5026 =
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    None env app comp guard
                                   in
                                (match uu____5026 with
                                 | (comp,g) -> (app, comp, g)))))
                  in
               let rec tc_args head_info uu____5084 bs args =
                 match uu____5084 with
                 | (subst,outargs,arg_rets,g,fvs) ->
                     (match (bs, args) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____5179))::rest,
                         (uu____5181,None )::uu____5182) ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t = check_no_escape (Some head) env fvs t  in
                          let uu____5219 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head.FStar_Syntax_Syntax.pos env t
                             in
                          (match uu____5219 with
                           | (varg,uu____5230,implicits) ->
                               let subst = (FStar_Syntax_Syntax.NT (x, varg))
                                 :: subst  in
                               let arg =
                                 let _0_468 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, _0_468)  in
                               let _0_470 =
                                 let _0_469 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t))) :: outargs), (arg ::
                                   arg_rets), _0_469, fvs)
                                  in
                               tc_args head_info _0_470 rest args)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____5333 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x =
                              let uu___107_5340 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___107_5340.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___107_5340.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____5342 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____5342
                             then
                               let _0_471 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n" _0_471
                             else ());
                            (let targ =
                               check_no_escape (Some head) env fvs targ  in
                             let env =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ
                                in
                             let env =
                               let uu___108_5347 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___108_5347.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___108_5347.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___108_5347.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___108_5347.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___108_5347.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___108_5347.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___108_5347.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___108_5347.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___108_5347.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___108_5347.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___108_5347.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___108_5347.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___108_5347.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___108_5347.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___108_5347.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___108_5347.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___108_5347.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___108_5347.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___108_5347.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___108_5347.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___108_5347.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___108_5347.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___108_5347.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             (let uu____5349 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.High
                                 in
                              if uu____5349
                              then
                                let _0_474 = FStar_Syntax_Print.tag_of_term e
                                   in
                                let _0_473 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let _0_472 =
                                  FStar_Syntax_Print.term_to_string targ  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n" _0_474
                                  _0_473 _0_472
                              else ());
                             (let uu____5351 = tc_term env e  in
                              match uu____5351 with
                              | (e,c,g_e) ->
                                  let g =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e, aq)  in
                                  let uu____5367 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c
                                     in
                                  if uu____5367
                                  then
                                    let subst =
                                      let _0_475 = FStar_List.hd bs  in
                                      maybe_extend_subst subst _0_475 e  in
                                    tc_args head_info
                                      (subst,
                                        ((arg, None,
                                           (FStar_Util.Inl
                                              ((c.FStar_Syntax_Syntax.lcomp_name),
                                                (c.FStar_Syntax_Syntax.lcomp_res_typ))))
                                        :: outargs), (arg :: arg_rets), g,
                                        fvs) rest rest'
                                  else
                                    (let uu____5427 =
                                       FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env c.FStar_Syntax_Syntax.lcomp_name
                                        in
                                     if uu____5427
                                     then
                                       let subst =
                                         let _0_476 = FStar_List.hd bs  in
                                         maybe_extend_subst subst _0_476 e
                                          in
                                       tc_args head_info
                                         (subst,
                                           ((arg, (Some x),
                                              (FStar_Util.Inr c)) ::
                                           outargs), (arg :: arg_rets), g,
                                           fvs) rest rest'
                                     else
                                       (let uu____5477 =
                                          FStar_Syntax_Syntax.is_null_binder
                                            (FStar_List.hd bs)
                                           in
                                        if uu____5477
                                        then
                                          let newx =
                                            FStar_Syntax_Syntax.new_bv
                                              (Some
                                                 (e.FStar_Syntax_Syntax.pos))
                                              c.FStar_Syntax_Syntax.lcomp_res_typ
                                             in
                                          let arg' =
                                            let _0_477 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                newx
                                               in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              _0_477
                                             in
                                          tc_args head_info
                                            (subst,
                                              ((arg, (Some newx),
                                                 (FStar_Util.Inr c)) ::
                                              outargs), (arg' :: arg_rets),
                                              g, fvs) rest rest'
                                        else
                                          (let _0_480 =
                                             let _0_479 =
                                               let _0_478 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   (FStar_Syntax_Syntax.bv_to_name
                                                      x)
                                                  in
                                               _0_478 :: arg_rets  in
                                             (subst,
                                               ((arg, (Some x),
                                                  (FStar_Util.Inr c)) ::
                                               outargs), _0_479, g, (x ::
                                               fvs))
                                              in
                                           tc_args head_info _0_480 rest
                                             rest')))))))
                      | (uu____5559,[]) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____5580) ->
                          let uu____5610 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs []
                             in
                          (match uu____5610 with
                           | (head,chead,ghead) ->
                               let rec aux norm tres =
                                 let tres =
                                   let _0_481 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right _0_481
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,cres') ->
                                     let uu____5648 =
                                       FStar_Syntax_Subst.open_comp bs cres'
                                        in
                                     (match uu____5648 with
                                      | (bs,cres') ->
                                          let head_info =
                                            let _0_482 =
                                              FStar_TypeChecker_Env.lcomp_of_comp
                                                env cres'
                                               in
                                            (head, chead, ghead, _0_482)  in
                                          ((let uu____5662 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____5662
                                            then
                                              let _0_483 =
                                                FStar_Range.string_of_range
                                                  tres.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                _0_483
                                            else ());
                                           tc_args head_info
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs args))
                                 | uu____5692 when Prims.op_Negation norm ->
                                     let _0_484 = unfold_whnf env tres  in
                                     aux true _0_484
                                 | uu____5693 ->
                                     Prims.raise
                                       (FStar_Errors.Error
                                          (let _0_488 =
                                             let _0_486 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env thead
                                                in
                                             let _0_485 =
                                               FStar_Util.string_of_int
                                                 n_args
                                                in
                                             FStar_Util.format2
                                               "Too many arguments to function of type %s; got %s arguments"
                                               _0_486 _0_485
                                              in
                                           let _0_487 =
                                             FStar_Syntax_Syntax.argpos arg
                                              in
                                           (_0_488, _0_487)))
                                  in
                               aux false
                                 chead.FStar_Syntax_Syntax.lcomp_res_typ))
                  in
               let rec check_function_app norm tf =
                 let uu____5712 =
                   (FStar_Syntax_Util.unrefine tf).FStar_Syntax_Syntax.n  in
                 match uu____5712 with
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
                           let uu____5786 = tc_term env e  in
                           (match uu____5786 with
                            | (e,c,g_e) ->
                                let uu____5799 = tc_args env tl  in
                                (match uu____5799 with
                                 | (args,comps,g_rest) ->
                                     let _0_489 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e, imp) :: args),
                                       (((e.FStar_Syntax_Syntax.pos), c) ::
                                       comps), _0_489)))
                        in
                     let uu____5831 = tc_args env args  in
                     (match uu____5831 with
                      | (args,comps,g_args) ->
                          let bs =
                            FStar_Syntax_Util.null_binders_of_tks
                              (FStar_All.pipe_right comps
                                 (FStar_List.map
                                    (fun uu____5869  ->
                                       match uu____5869 with
                                       | (uu____5877,c) ->
                                           ((c.FStar_Syntax_Syntax.lcomp_res_typ),
                                             None))))
                             in
                          let ml_or_tot t r =
                            let uu____5889 = FStar_Options.ml_ish ()  in
                            if uu____5889
                            then FStar_Syntax_Util.ml_comp t r
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let _0_492 =
                              let _0_491 =
                                let _0_490 = FStar_Syntax_Util.type_u ()  in
                                FStar_All.pipe_right _0_490 Prims.fst  in
                              FStar_TypeChecker_Util.new_uvar env _0_491  in
                            ml_or_tot _0_492 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____5896 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____5896
                            then
                              let _0_495 =
                                FStar_Syntax_Print.term_to_string head  in
                              let _0_494 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let _0_493 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                _0_495 _0_494 _0_493
                            else ());
                           (let _0_496 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              _0_496);
                           (let comp =
                              let _0_497 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.lcomp_of_comp env)
                                  cres
                                 in
                              FStar_List.fold_right
                                (fun uu____5902  ->
                                   fun out  ->
                                     match uu____5902 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind env None
                                           c (None, out))
                                (((head.FStar_Syntax_Syntax.pos), chead) ::
                                comps) _0_497
                               in
                            let _0_499 =
                              (FStar_Syntax_Syntax.mk_Tm_app head args)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                                r
                               in
                            let _0_498 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (_0_499, comp, _0_498))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____5931 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____5931 with
                      | (bs,c) ->
                          let head_info =
                            let _0_500 =
                              FStar_TypeChecker_Env.lcomp_of_comp env c  in
                            (head, chead, ghead, _0_500)  in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs args)
                 | uu____5974 ->
                     if Prims.op_Negation norm
                     then
                       let _0_501 = unfold_whnf env tf  in
                       check_function_app true _0_501
                     else
                       Prims.raise
                         (FStar_Errors.Error
                            (let _0_502 =
                               FStar_TypeChecker_Err.expected_function_typ
                                 env tf
                                in
                             (_0_502, (head.FStar_Syntax_Syntax.pos))))
                  in
               let _0_504 =
                 let _0_503 = FStar_Syntax_Util.unrefine thead  in
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.WHNF] env _0_503
                  in
               check_function_app false _0_504)

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
                FStar_Syntax_Subst.compress
                  chead.FStar_Syntax_Syntax.lcomp_res_typ
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_TypeChecker_Env.result_typ env c  in
                  let uu____6029 =
                    FStar_List.fold_left2
                      (fun uu____6042  ->
                         fun uu____6043  ->
                           fun uu____6044  ->
                             match (uu____6042, uu____6043, uu____6044) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____6088 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____6088 with
                                   | (e,c,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen
                                          in
                                       let g =
                                         let _0_505 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           _0_505 g
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
                                                    c.FStar_Syntax_Syntax.lcomp_name)))
                                          in
                                       let _0_509 =
                                         let _0_507 =
                                           let _0_506 =
                                             FStar_Syntax_Syntax.as_arg e  in
                                           [_0_506]  in
                                         FStar_List.append seen _0_507  in
                                       let _0_508 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g
                                          in
                                       (_0_509, _0_508, ghost))))
                      ([], g_head, false) args bs
                     in
                  (match uu____6029 with
                   | (args,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head args)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r
                          in
                       let c =
                         if ghost
                         then
                           let _0_510 = FStar_Syntax_Syntax.mk_GTotal res_t
                              in
                           FStar_All.pipe_right _0_510
                             (FStar_TypeChecker_Env.lcomp_of_comp env)
                         else FStar_TypeChecker_Env.lcomp_of_comp env c  in
                       let uu____6134 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c guard
                          in
                       (match uu____6134 with | (c,g) -> (e, c, g)))
              | uu____6146 ->
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
        let uu____6168 = FStar_Syntax_Subst.open_branch branch  in
        match uu____6168 with
        | (pattern,when_clause,branch_exp) ->
            let uu____6194 = branch  in
            (match uu____6194 with
             | (cpat,uu____6214,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____6256 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0
                      in
                   match uu____6256 with
                   | (pat_bvs,exps,p) ->
                       ((let uu____6278 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____6278
                         then
                           let _0_512 = FStar_Syntax_Print.pat_to_string p0
                              in
                           let _0_511 = FStar_Syntax_Print.pat_to_string p
                              in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             _0_512 _0_511
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs
                            in
                         let uu____6281 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____6281 with
                         | (env1,uu____6294) ->
                             let env1 =
                               let uu___109_6298 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___109_6298.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___109_6298.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___109_6298.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___109_6298.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___109_6298.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___109_6298.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___109_6298.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___109_6298.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___109_6298.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___109_6298.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___109_6298.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___109_6298.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___109_6298.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___109_6298.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___109_6298.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___109_6298.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___109_6298.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___109_6298.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___109_6298.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___109_6298.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___109_6298.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___109_6298.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___109_6298.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             let uu____6300 =
                               let _0_528 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____6320 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High
                                             in
                                          if uu____6320
                                          then
                                            let _0_514 =
                                              FStar_Syntax_Print.term_to_string
                                                e
                                               in
                                            let _0_513 =
                                              FStar_Syntax_Print.term_to_string
                                                pat_t
                                               in
                                            FStar_Util.print2
                                              "Checking pattern expression %s against expected type %s\n"
                                              _0_514 _0_513
                                          else ());
                                         (let uu____6322 = tc_term env1 e  in
                                          match uu____6322 with
                                          | (e,lc,g) ->
                                              ((let uu____6332 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High
                                                   in
                                                if uu____6332
                                                then
                                                  let _0_516 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env e
                                                     in
                                                  let _0_515 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env
                                                      lc.FStar_Syntax_Syntax.lcomp_res_typ
                                                     in
                                                  FStar_Util.print2
                                                    "Pre-checked pattern expression %s at type %s\n"
                                                    _0_516 _0_515
                                                else ());
                                               (let g' =
                                                  FStar_TypeChecker_Rel.teq
                                                    env
                                                    lc.FStar_Syntax_Syntax.lcomp_res_typ
                                                    expected_pat_t
                                                   in
                                                let g =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g'
                                                   in
                                                let uu____6336 =
                                                  let _0_517 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___110_6337 = g
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___110_6337.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___110_6337.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___110_6337.FStar_TypeChecker_Env.implicits)
                                                       })
                                                     in
                                                  FStar_All.pipe_right _0_517
                                                    FStar_TypeChecker_Rel.resolve_implicits
                                                   in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e
                                                   in
                                                let uvars_to_string uvs =
                                                  let _0_519 =
                                                    let _0_518 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements
                                                       in
                                                    FStar_All.pipe_right
                                                      _0_518
                                                      (FStar_List.map
                                                         (fun uu____6371  ->
                                                            match uu____6371
                                                            with
                                                            | (u,uu____6376)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u))
                                                     in
                                                  FStar_All.pipe_right _0_519
                                                    (FStar_String.concat ", ")
                                                   in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e'
                                                   in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t
                                                   in
                                                (let uu____6388 =
                                                   let _0_520 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2
                                                      in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation _0_520
                                                    in
                                                 if uu____6388
                                                 then
                                                   let unresolved =
                                                     let _0_521 =
                                                       FStar_Util.set_difference
                                                         uvs1 uvs2
                                                        in
                                                     FStar_All.pipe_right
                                                       _0_521
                                                       FStar_Util.set_elements
                                                      in
                                                   Prims.raise
                                                     (FStar_Errors.Error
                                                        (let _0_526 =
                                                           let _0_525 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e'
                                                              in
                                                           let _0_524 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env
                                                               expected_pat_t
                                                              in
                                                           let _0_523 =
                                                             let _0_522 =
                                                               FStar_All.pipe_right
                                                                 unresolved
                                                                 (FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____6416
                                                                     ->
                                                                    match uu____6416
                                                                    with
                                                                    | 
                                                                    (u,uu____6424)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u))
                                                                in
                                                             FStar_All.pipe_right
                                                               _0_522
                                                               (FStar_String.concat
                                                                  ", ")
                                                              in
                                                           FStar_Util.format3
                                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                             _0_525 _0_524
                                                             _0_523
                                                            in
                                                         (_0_526,
                                                           (p.FStar_Syntax_Syntax.p))))
                                                 else ());
                                                (let uu____6438 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High
                                                    in
                                                 if uu____6438
                                                 then
                                                   let _0_527 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env e
                                                      in
                                                   FStar_Util.print1
                                                     "Done checking pattern expression %s\n"
                                                     _0_527
                                                 else ());
                                                (e, e'))))))
                                  in
                               FStar_All.pipe_right _0_528 FStar_List.unzip
                                in
                             (match uu____6300 with
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
                 let uu____6462 =
                   let _0_529 = FStar_TypeChecker_Env.push_bv env scrutinee
                      in
                   FStar_All.pipe_right _0_529
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____6462 with
                  | (scrutinee_env,uu____6478) ->
                      let uu____6481 = tc_pat true pat_t pattern  in
                      (match uu____6481 with
                       | (pattern,pat_bvs,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____6509 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____6524 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____6524
                                 then
                                   Prims.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____6532 =
                                      let _0_530 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool
                                         in
                                      tc_term _0_530 e  in
                                    match uu____6532 with
                                    | (e,c,g) -> ((Some e), g))
                              in
                           (match uu____6509 with
                            | (when_clause,g_when) ->
                                let uu____6555 = tc_term pat_env branch_exp
                                   in
                                (match uu____6555 with
                                 | (branch_exp,c,g_branch) ->
                                     let when_condition =
                                       match when_clause with
                                       | None  -> None
                                       | Some w ->
                                           let _0_532 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_531  -> Some _0_531)
                                             _0_532
                                        in
                                     let uu____6575 =
                                       let eqs =
                                         let uu____6581 =
                                           Prims.op_Negation
                                             (FStar_TypeChecker_Env.should_verify
                                                env)
                                            in
                                         if uu____6581
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
                                                     | uu____6595 ->
                                                         let clause =
                                                           let _0_533 =
                                                             env.FStar_TypeChecker_Env.universe_of
                                                               env pat_t
                                                              in
                                                           FStar_Syntax_Util.mk_eq2
                                                             _0_533 pat_t
                                                             scrutinee_tm e
                                                            in
                                                         (match fopt with
                                                          | None  ->
                                                              Some clause
                                                          | Some f ->
                                                              let _0_535 =
                                                                FStar_Syntax_Util.mk_disj
                                                                  clause f
                                                                 in
                                                              FStar_All.pipe_left
                                                                (fun _0_534 
                                                                   ->
                                                                   Some
                                                                    _0_534)
                                                                _0_535)) None)
                                          in
                                       let uu____6606 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp c g_branch
                                          in
                                       match uu____6606 with
                                       | (c,g_branch) ->
                                           let uu____6616 =
                                             match (eqs, when_condition) with
                                             | uu____6623 when
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
                                                 let _0_537 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c gf
                                                    in
                                                 let _0_536 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (_0_537, _0_536)
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
                                                 let _0_540 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c g_fw
                                                    in
                                                 let _0_539 =
                                                   let _0_538 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     _0_538 g_when
                                                    in
                                                 (_0_540, _0_539)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let _0_541 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c g_w
                                                    in
                                                 (_0_541, g_when)
                                              in
                                           (match uu____6616 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs
                                                   in
                                                let _0_543 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs c_weak
                                                   in
                                                let _0_542 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    binders g_when_weak
                                                   in
                                                (_0_543, _0_542, g_branch))
                                        in
                                     (match uu____6575 with
                                      | (c,g_when,g_branch) ->
                                          let branch_guard =
                                            let uu____6665 =
                                              Prims.op_Negation
                                                (FStar_TypeChecker_Env.should_verify
                                                   env)
                                               in
                                            if uu____6665
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm pat_exp =
                                                 let discriminate
                                                   scrutinee_tm f =
                                                   let uu____6696 =
                                                     let _0_545 =
                                                       FStar_List.length
                                                         (Prims.snd
                                                            (let _0_544 =
                                                               FStar_TypeChecker_Env.typ_of_datacon
                                                                 env
                                                                 f.FStar_Syntax_Syntax.v
                                                                in
                                                             FStar_TypeChecker_Env.datacons_of_typ
                                                               env _0_544))
                                                        in
                                                     _0_545 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____6696
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____6707 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____6707 with
                                                     | None  -> []
                                                     | uu____6714 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None
                                                            in
                                                         let disc =
                                                           (let _0_547 =
                                                              let _0_546 =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  scrutinee_tm
                                                                 in
                                                              [_0_546]  in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              disc _0_547)
                                                             None
                                                             scrutinee_tm.FStar_Syntax_Syntax.pos
                                                            in
                                                         let _0_548 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc
                                                             FStar_Syntax_Const.exp_true_bool
                                                            in
                                                         [_0_548]
                                                   else []  in
                                                 let fail uu____6733 =
                                                   failwith
                                                     (let _0_551 =
                                                        FStar_Range.string_of_range
                                                          pat_exp.FStar_Syntax_Syntax.pos
                                                         in
                                                      let _0_550 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp
                                                         in
                                                      let _0_549 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        _0_551 _0_550 _0_549)
                                                    in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t,uu____6754) ->
                                                       head_constructor t
                                                   | uu____6760 -> fail ()
                                                    in
                                                 let pat_exp =
                                                   let _0_552 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp
                                                      in
                                                   FStar_All.pipe_right
                                                     _0_552
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
                                                     let _0_554 =
                                                       let _0_553 =
                                                         tc_constant
                                                           pat_exp.FStar_Syntax_Syntax.pos
                                                           c
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         _0_553 scrutinee_tm
                                                         pat_exp
                                                        in
                                                     [_0_554]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                   _
                                                   |FStar_Syntax_Syntax.Tm_fvar
                                                   _ ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp
                                                        in
                                                     let uu____6786 =
                                                       Prims.op_Negation
                                                         (FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v)
                                                        in
                                                     if uu____6786
                                                     then []
                                                     else
                                                       (let _0_555 =
                                                          head_constructor
                                                            pat_exp
                                                           in
                                                        discriminate
                                                          scrutinee_tm _0_555)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head,args) ->
                                                     let f =
                                                       head_constructor head
                                                        in
                                                     let uu____6816 =
                                                       Prims.op_Negation
                                                         (FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v)
                                                        in
                                                     if uu____6816
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let _0_559 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____6841
                                                                     ->
                                                                    match uu____6841
                                                                    with
                                                                    | 
                                                                    (ei,uu____6848)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____6858
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____6858
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____6865
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    (let _0_558
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None  in
                                                                    let _0_557
                                                                    =
                                                                    let _0_556
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm
                                                                     in
                                                                    [_0_556]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    _0_558
                                                                    _0_557)
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            _0_559
                                                            FStar_List.flatten
                                                           in
                                                        let _0_560 =
                                                          discriminate
                                                            scrutinee_tm f
                                                           in
                                                        FStar_List.append
                                                          _0_560
                                                          sub_term_guards)
                                                 | uu____6886 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm pat =
                                                 let uu____6898 =
                                                   Prims.op_Negation
                                                     (FStar_TypeChecker_Env.should_verify
                                                        env)
                                                    in
                                                 if uu____6898
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let _0_561 =
                                                        build_branch_guard
                                                          scrutinee_tm pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        _0_561
                                                       in
                                                    let uu____6902 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____6902 with
                                                    | (k,uu____6906) ->
                                                        let uu____6907 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____6907
                                                         with
                                                         | (t,uu____6912,uu____6913)
                                                             -> t))
                                                  in
                                               let branch_guard =
                                                 let _0_562 =
                                                   FStar_All.pipe_right
                                                     norm_disj_exps
                                                     (FStar_List.map
                                                        (build_and_check_branch_guard
                                                           scrutinee_tm))
                                                    in
                                                 FStar_All.pipe_right _0_562
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
                                          ((let uu____6924 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____6924
                                            then
                                              let _0_563 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                _0_563
                                            else ());
                                           (let _0_564 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern, when_clause,
                                                  branch_exp)
                                               in
                                            (_0_564, branch_guard, c, guard)))))))))

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
          let uu____6943 = check_let_bound_def true env lb  in
          (match uu____6943 with
           | (e1,univ_vars,c1,g1,annotated) ->
               let uu____6957 =
                 if
                   annotated &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then (g1, e1, univ_vars, c1)
                 else
                   (let g1 =
                      let _0_565 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env
                          g1
                         in
                      FStar_All.pipe_right _0_565
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____6969 =
                      FStar_List.hd
                        (let _0_568 =
                           let _0_567 =
                             let _0_566 =
                               c1.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                             ((lb.FStar_Syntax_Syntax.lbname), e1, _0_566)
                              in
                           [_0_567]  in
                         FStar_TypeChecker_Util.generalize env _0_568)
                       in
                    match uu____6969 with
                    | (uu____7000,univs,e1,c1) ->
                        let _0_569 =
                          FStar_TypeChecker_Env.lcomp_of_comp env c1  in
                        (g1, e1, univs, _0_569))
                  in
               (match uu____6957 with
                | (g1,e1,univ_vars,c1) ->
                    let uu____7011 =
                      let uu____7016 =
                        FStar_TypeChecker_Env.should_verify env  in
                      if uu____7016
                      then
                        let uu____7021 =
                          FStar_TypeChecker_Util.check_top_level env g1 c1
                           in
                        match uu____7021 with
                        | (ok,c1) ->
                            (if ok
                             then (e2, c1)
                             else
                               ((let uu____7038 =
                                   FStar_Options.warn_top_level_effects ()
                                    in
                                 if uu____7038
                                 then
                                   let _0_570 =
                                     FStar_TypeChecker_Env.get_range env  in
                                   FStar_Errors.warn _0_570
                                     FStar_TypeChecker_Err.top_level_effect
                                 else ());
                                (let _0_571 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos
                                    in
                                 (_0_571, c1))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                         (let c =
                            let _0_572 =
                              c1.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                            FStar_All.pipe_right _0_572
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env)
                             in
                          let e2 =
                            let uu____7064 = FStar_Syntax_Util.is_pure_comp c
                               in
                            if uu____7064
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
                    (match uu____7011 with
                     | (e2,c1) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env
                             (FStar_Syntax_Util.comp_effect_name c1)
                             FStar_Syntax_Syntax.U_zero
                             FStar_TypeChecker_Common.t_unit
                            in
                         let cres =
                           let _0_573 =
                             FStar_Syntax_Util.ml_comp
                               FStar_TypeChecker_Common.t_unit
                               e.FStar_Syntax_Syntax.pos
                              in
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.lcomp_of_comp env) _0_573
                            in
                         (FStar_ST.write e2.FStar_Syntax_Syntax.tk
                            (Some
                               (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                          (let lb =
                             let _0_574 =
                               FStar_TypeChecker_Env.result_typ env c1  in
                             FStar_Syntax_Util.close_univs_and_mk_letbinding
                               None lb.FStar_Syntax_Syntax.lbname univ_vars
                               _0_574 (FStar_Syntax_Util.comp_effect_name c1)
                               e1
                              in
                           let _0_575 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb]), e2)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos
                              in
                           (_0_575, cres,
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____7117 -> failwith "Impossible"

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
            let uu___111_7138 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___111_7138.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___111_7138.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___111_7138.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___111_7138.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___111_7138.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___111_7138.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___111_7138.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___111_7138.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___111_7138.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___111_7138.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___111_7138.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___111_7138.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___111_7138.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___111_7138.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___111_7138.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___111_7138.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___111_7138.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___111_7138.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___111_7138.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___111_7138.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___111_7138.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___111_7138.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___111_7138.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____7139 =
            let _0_577 =
              let _0_576 = FStar_TypeChecker_Env.clear_expected_typ env  in
              FStar_All.pipe_right _0_576 Prims.fst  in
            check_let_bound_def false _0_577 lb  in
          (match uu____7139 with
           | (e1,uu____7153,c1,g1,annotated) ->
               let x =
                 let uu___112_7158 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___112_7158.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___112_7158.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.lcomp_res_typ)
                 }  in
               let uu____7159 =
                 let _0_579 =
                   let _0_578 = FStar_Syntax_Syntax.mk_binder x  in [_0_578]
                    in
                 FStar_Syntax_Subst.open_term _0_579 e2  in
               (match uu____7159 with
                | (xb,e2) ->
                    let xbinder = FStar_List.hd xb  in
                    let x = Prims.fst xbinder  in
                    let uu____7173 =
                      let _0_580 = FStar_TypeChecker_Env.push_bv env x  in
                      tc_term _0_580 e2  in
                    (match uu____7173 with
                     | (e2,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.bind env (Some e1) c1
                             ((Some x), c2)
                            in
                         let e1 =
                           FStar_TypeChecker_Util.maybe_lift env e1
                             c1.FStar_Syntax_Syntax.lcomp_name
                             cres.FStar_Syntax_Syntax.lcomp_name
                             c1.FStar_Syntax_Syntax.lcomp_res_typ
                            in
                         let e2 =
                           FStar_TypeChecker_Util.maybe_lift env e2
                             c2.FStar_Syntax_Syntax.lcomp_name
                             cres.FStar_Syntax_Syntax.lcomp_name
                             c2.FStar_Syntax_Syntax.lcomp_res_typ
                            in
                         let lb =
                           FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl x)
                             [] c1.FStar_Syntax_Syntax.lcomp_res_typ
                             c1.FStar_Syntax_Syntax.lcomp_name e1
                            in
                         let e =
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 (let _0_581 = FStar_Syntax_Subst.close xb e2
                                     in
                                  ((false, [lb]), _0_581))))
                             (Some
                                ((cres.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos
                            in
                         let e =
                           FStar_TypeChecker_Util.maybe_monadic env e
                             cres.FStar_Syntax_Syntax.lcomp_name
                             cres.FStar_Syntax_Syntax.lcomp_res_typ
                            in
                         let x_eq_e1 =
                           let _0_585 =
                             let _0_584 =
                               env.FStar_TypeChecker_Env.universe_of env
                                 c1.FStar_Syntax_Syntax.lcomp_res_typ
                                in
                             let _0_583 = FStar_Syntax_Syntax.bv_to_name x
                                in
                             FStar_Syntax_Util.mk_eq2 _0_584
                               c1.FStar_Syntax_Syntax.lcomp_res_typ _0_583 e1
                              in
                           FStar_All.pipe_left
                             (fun _0_582  ->
                                FStar_TypeChecker_Common.NonTrivial _0_582)
                             _0_585
                            in
                         let g2 =
                           let _0_587 =
                             let _0_586 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard _0_586 g2  in
                           FStar_TypeChecker_Rel.close_guard xb _0_587  in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g2
                            in
                         let uu____7207 =
                           FStar_Option.isSome
                             (FStar_TypeChecker_Env.expected_typ env)
                            in
                         if uu____7207
                         then
                           let tt =
                             let _0_588 =
                               FStar_TypeChecker_Env.expected_typ env  in
                             FStar_All.pipe_right _0_588 FStar_Option.get  in
                           ((let uu____7214 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____7214
                             then
                               let _0_590 =
                                 FStar_Syntax_Print.term_to_string tt  in
                               let _0_589 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.lcomp_res_typ
                                  in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.lcomp_res_typ=%s\n"
                                 _0_590 _0_589
                             else ());
                            (e, cres, guard))
                         else
                           (let t =
                              check_no_escape None env [x]
                                cres.FStar_Syntax_Syntax.lcomp_res_typ
                               in
                            (let uu____7219 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____7219
                             then
                               let _0_592 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.lcomp_res_typ
                                  in
                               let _0_591 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 _0_592 _0_591
                             else ());
                            (e,
                              ((let uu___113_7221 = cres  in
                                {
                                  FStar_Syntax_Syntax.lcomp_name =
                                    (uu___113_7221.FStar_Syntax_Syntax.lcomp_name);
                                  FStar_Syntax_Syntax.lcomp_univs =
                                    (uu___113_7221.FStar_Syntax_Syntax.lcomp_univs);
                                  FStar_Syntax_Syntax.lcomp_indices =
                                    (uu___113_7221.FStar_Syntax_Syntax.lcomp_indices);
                                  FStar_Syntax_Syntax.lcomp_res_typ = t;
                                  FStar_Syntax_Syntax.lcomp_cflags =
                                    (uu___113_7221.FStar_Syntax_Syntax.lcomp_cflags);
                                  FStar_Syntax_Syntax.lcomp_as_comp =
                                    (uu___113_7221.FStar_Syntax_Syntax.lcomp_as_comp)
                                })), guard)))))
      | uu____7222 -> failwith "Impossible"

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
          let uu____7243 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____7243 with
           | (lbs,e2) ->
               let uu____7254 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____7254 with
                | (env0,topt) ->
                    let uu____7265 = build_let_rec_env true env0 lbs  in
                    (match uu____7265 with
                     | (lbs,rec_env) ->
                         let uu____7276 = check_let_recs rec_env lbs  in
                         (match uu____7276 with
                          | (lbs,g_lbs) ->
                              let g_lbs =
                                let _0_593 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env g_lbs
                                   in
                                FStar_All.pipe_right _0_593
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let _0_595 =
                                  FStar_All.pipe_right lbs
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right _0_595
                                  (fun _0_594  -> Some _0_594)
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
                                     let _0_597 =
                                       FStar_All.pipe_right lbs
                                         (FStar_List.map
                                            (fun lb  ->
                                               let _0_596 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 _0_596)))
                                        in
                                     FStar_TypeChecker_Util.generalize env
                                       _0_597
                                      in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____7347  ->
                                           match uu____7347 with
                                           | (x,uvs,e,c) ->
                                               let _0_598 =
                                                 FStar_TypeChecker_Env.result_typ
                                                   env c
                                                  in
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs _0_598
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e)))
                                 in
                              let cres =
                                let _0_599 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit
                                   in
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.lcomp_of_comp env)
                                  _0_599
                                 in
                              (FStar_ST.write e2.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____7370 =
                                  FStar_Syntax_Subst.close_let_rec lbs e2  in
                                match uu____7370 with
                                | (lbs,e2) ->
                                    let _0_601 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs), e2)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let _0_600 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env g_lbs
                                       in
                                    (_0_601, cres, _0_600)))))))
      | uu____7399 -> failwith "Impossible"

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
          let uu____7420 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____7420 with
           | (lbs,e2) ->
               let uu____7431 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               (match uu____7431 with
                | (env0,topt) ->
                    let uu____7442 = build_let_rec_env false env0 lbs  in
                    (match uu____7442 with
                     | (lbs,rec_env) ->
                         let uu____7453 = check_let_recs rec_env lbs  in
                         (match uu____7453 with
                          | (lbs,g_lbs) ->
                              let uu____7464 =
                                FStar_All.pipe_right lbs
                                  (FStar_Util.fold_map
                                     (fun env  ->
                                        fun lb  ->
                                          let x =
                                            let uu___114_7475 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___114_7475.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___114_7475.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb =
                                            let uu___115_7477 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___115_7477.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___115_7477.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___115_7477.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___115_7477.FStar_Syntax_Syntax.lbdef)
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
                              (match uu____7464 with
                               | (env,lbs) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____7494 = tc_term env e2  in
                                   (match uu____7494 with
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
                                            cres.FStar_Syntax_Syntax.lcomp_res_typ
                                           in
                                        let cres =
                                          let uu___116_7508 = cres  in
                                          {
                                            FStar_Syntax_Syntax.lcomp_name =
                                              (uu___116_7508.FStar_Syntax_Syntax.lcomp_name);
                                            FStar_Syntax_Syntax.lcomp_univs =
                                              (uu___116_7508.FStar_Syntax_Syntax.lcomp_univs);
                                            FStar_Syntax_Syntax.lcomp_indices
                                              =
                                              (uu___116_7508.FStar_Syntax_Syntax.lcomp_indices);
                                            FStar_Syntax_Syntax.lcomp_res_typ
                                              = tres;
                                            FStar_Syntax_Syntax.lcomp_cflags
                                              =
                                              (uu___116_7508.FStar_Syntax_Syntax.lcomp_cflags);
                                            FStar_Syntax_Syntax.lcomp_as_comp
                                              =
                                              (uu___116_7508.FStar_Syntax_Syntax.lcomp_as_comp)
                                          }  in
                                        let uu____7509 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs e2
                                           in
                                        (match uu____7509 with
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
                                              | Some uu____7538 ->
                                                  (e, cres, guard)
                                              | None  ->
                                                  let tres =
                                                    check_no_escape None env
                                                      bvs tres
                                                     in
                                                  let cres =
                                                    let uu___117_7543 = cres
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.lcomp_name
                                                        =
                                                        (uu___117_7543.FStar_Syntax_Syntax.lcomp_name);
                                                      FStar_Syntax_Syntax.lcomp_univs
                                                        =
                                                        (uu___117_7543.FStar_Syntax_Syntax.lcomp_univs);
                                                      FStar_Syntax_Syntax.lcomp_indices
                                                        =
                                                        (uu___117_7543.FStar_Syntax_Syntax.lcomp_indices);
                                                      FStar_Syntax_Syntax.lcomp_res_typ
                                                        = tres;
                                                      FStar_Syntax_Syntax.lcomp_cflags
                                                        =
                                                        (uu___117_7543.FStar_Syntax_Syntax.lcomp_cflags);
                                                      FStar_Syntax_Syntax.lcomp_as_comp
                                                        =
                                                        (uu___117_7543.FStar_Syntax_Syntax.lcomp_as_comp)
                                                    }  in
                                                  (e, cres, guard)))))))))
      | uu____7546 -> failwith "Impossible"

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
          let uu____7562 = FStar_Syntax_Util.arrow_formals_comp t  in
          match uu____7562 with
          | (uu____7568,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c)
                 in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)
           in
        let uu____7579 =
          FStar_List.fold_left
            (fun uu____7586  ->
               fun lb  ->
                 match uu____7586 with
                 | (lbs,env) ->
                     let uu____7598 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env
                         lb
                        in
                     (match uu____7598 with
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
                              (let uu____7612 =
                                 let _0_603 =
                                   let _0_602 = FStar_Syntax_Util.type_u ()
                                      in
                                   FStar_All.pipe_left Prims.fst _0_602  in
                                 tc_check_tot_or_gtot_term
                                   (let uu___118_7616 = env0  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___118_7616.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___118_7616.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___118_7616.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___118_7616.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___118_7616.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___118_7616.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___118_7616.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___118_7616.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___118_7616.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___118_7616.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___118_7616.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___118_7616.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___118_7616.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___118_7616.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___118_7616.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___118_7616.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___118_7616.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___118_7616.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___118_7616.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___118_7616.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___118_7616.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___118_7616.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___118_7616.FStar_TypeChecker_Env.qname_and_index)
                                    }) t _0_603
                                  in
                               match uu____7612 with
                               | (t,uu____7620,g) ->
                                   let g =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let _0_604 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env g
                                        in
                                     FStar_All.pipe_left Prims.ignore _0_604);
                                    norm env0 t))
                             in
                          let env =
                            let uu____7625 =
                              (termination_check_enabled t) &&
                                (FStar_TypeChecker_Env.should_verify env)
                               in
                            if uu____7625
                            then
                              let uu___119_7626 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___119_7626.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___119_7626.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___119_7626.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___119_7626.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___119_7626.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___119_7626.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___119_7626.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___119_7626.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___119_7626.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___119_7626.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___119_7626.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___119_7626.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t) ::
                                  (env.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___119_7626.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___119_7626.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___119_7626.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___119_7626.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___119_7626.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___119_7626.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___119_7626.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___119_7626.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___119_7626.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___119_7626.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___119_7626.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env
                                lb.FStar_Syntax_Syntax.lbname ([], t)
                             in
                          let lb =
                            let uu___120_7636 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_7636.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars;
                              FStar_Syntax_Syntax.lbtyp = t;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_7636.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb :: lbs), env))) ([], env) lbs
           in
        match uu____7579 with | (lbs,env) -> ((FStar_List.rev lbs), env)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____7650 =
        let _0_606 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____7669 =
                    let _0_605 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    tc_tot_or_gtot_term _0_605 lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____7669 with
                  | (e,c,g) ->
                      ((let uu____7679 =
                          Prims.op_Negation
                            (FStar_Syntax_Util.is_total_lcomp c)
                           in
                        if uu____7679
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
        FStar_All.pipe_right _0_606 FStar_List.unzip  in
      match uu____7650 with
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
        let uu____7701 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____7701 with
        | (env1,uu____7711) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____7717 = check_lbtyp top_level env lb  in
            (match uu____7717 with
             | (topt,wf_annot,univ_vars,univ_opening,env1) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e1 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____7743 =
                     tc_maybe_toplevel_term
                       (let uu___121_7747 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___121_7747.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___121_7747.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___121_7747.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___121_7747.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___121_7747.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___121_7747.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___121_7747.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___121_7747.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___121_7747.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___121_7747.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___121_7747.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___121_7747.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___121_7747.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___121_7747.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___121_7747.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___121_7747.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___121_7747.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___121_7747.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___121_7747.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___121_7747.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___121_7747.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___121_7747.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___121_7747.FStar_TypeChecker_Env.qname_and_index)
                        }) e1
                      in
                   match uu____7743 with
                   | (e1,c1,g1) ->
                       let uu____7756 =
                         let _0_607 =
                           FStar_TypeChecker_Env.set_range env1
                             e1.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____7761  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           _0_607 e1 c1 wf_annot
                          in
                       (match uu____7756 with
                        | (c1,guard_f) ->
                            let g1 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____7771 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____7771
                              then
                                let _0_610 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let _0_609 =
                                  FStar_Syntax_Print.term_to_string
                                    c1.FStar_Syntax_Syntax.lcomp_res_typ
                                   in
                                let _0_608 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1
                                   in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  _0_610 _0_609 _0_608
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
        | uu____7797 ->
            let uu____7798 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____7798 with
             | (univ_opening,univ_vars) ->
                 let t = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let _0_611 = FStar_TypeChecker_Env.set_expected_typ env1 t
                      in
                   ((Some t), FStar_TypeChecker_Rel.trivial_guard, univ_vars,
                     univ_opening, _0_611)
                 else
                   (let uu____7829 = FStar_Syntax_Util.type_u ()  in
                    match uu____7829 with
                    | (k,uu____7840) ->
                        let uu____7841 = tc_check_tot_or_gtot_term env1 t k
                           in
                        (match uu____7841 with
                         | (t,uu____7853,g) ->
                             ((let uu____7856 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____7856
                               then
                                 let _0_613 =
                                   FStar_Range.string_of_range
                                     (FStar_Syntax_Syntax.range_of_lbname
                                        lb.FStar_Syntax_Syntax.lbname)
                                    in
                                 let _0_612 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n" _0_613
                                   _0_612
                               else ());
                              (let t = norm env1 t  in
                               let _0_614 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t
                                  in
                               ((Some t), g, univ_vars, univ_opening, _0_614))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____7863  ->
      match uu____7863 with
      | (x,imp) ->
          let uu____7874 = FStar_Syntax_Util.type_u ()  in
          (match uu____7874 with
           | (tu,u) ->
               ((let uu____7886 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____7886
                 then
                   let _0_617 = FStar_Syntax_Print.bv_to_string x  in
                   let _0_616 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let _0_615 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     _0_617 _0_616 _0_615
                 else ());
                (let uu____7888 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____7888 with
                 | (t,uu____7899,g) ->
                     let x =
                       ((let uu___122_7904 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___122_7904.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___122_7904.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____7906 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____7906
                       then
                         let _0_619 =
                           FStar_Syntax_Print.bv_to_string (Prims.fst x)  in
                         let _0_618 = FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           _0_619 _0_618
                       else ());
                      (let _0_620 = push_binding env x  in (x, _0_620, g, u))))))

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
            let uu____7958 = tc_binder env b  in
            (match uu____7958 with
             | (b,env',g,u) ->
                 let uu____7981 = aux env' bs  in
                 (match uu____7981 with
                  | (bs,env',g',us) ->
                      let _0_622 =
                        let _0_621 = FStar_TypeChecker_Rel.close_guard [b] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g _0_621  in
                      ((b :: bs), env', _0_622, (u :: us))))
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
          (fun uu____8052  ->
             fun uu____8053  ->
               match (uu____8052, uu____8053) with
               | ((t,imp),(args,g)) ->
                   let uu____8090 = tc_term env t  in
                   (match uu____8090 with
                    | (t,uu____8100,g') ->
                        let _0_623 = FStar_TypeChecker_Rel.conj_guard g g'
                           in
                        (((t, imp) :: args), _0_623))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____8119  ->
             match uu____8119 with
             | (pats,g) ->
                 let uu____8133 = tc_args env p  in
                 (match uu____8133 with
                  | (args,g') ->
                      let _0_624 = FStar_TypeChecker_Rel.conj_guard g g'  in
                      ((args :: pats), _0_624))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____8148 = tc_maybe_toplevel_term env e  in
      match uu____8148 with
      | (e,c,g) ->
          let uu____8158 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____8158
          then (e, c, g)
          else
            (let g = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c = c.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             let c = norm_c env c  in
             let uu____8168 =
               let uu____8171 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c)
                  in
               if uu____8171
               then
                 let _0_625 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_TypeChecker_Env.result_typ env c)
                    in
                 (_0_625, false)
               else
                 (let _0_626 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_TypeChecker_Env.result_typ env c)
                     in
                  (_0_626, true))
                in
             match uu____8168 with
             | (target_comp,allow_ghost) ->
                 let uu____8180 =
                   FStar_TypeChecker_Rel.sub_comp env c target_comp  in
                 (match uu____8180 with
                  | Some g' ->
                      let _0_628 =
                        FStar_TypeChecker_Env.lcomp_of_comp env target_comp
                         in
                      let _0_627 = FStar_TypeChecker_Rel.conj_guard g g'  in
                      (e, _0_628, _0_627)
                  | uu____8186 ->
                      if allow_ghost
                      then
                        Prims.raise
                          (FStar_Errors.Error
                             (let _0_629 =
                                FStar_TypeChecker_Err.expected_ghost_expression
                                  e c
                                 in
                              (_0_629, (e.FStar_Syntax_Syntax.pos))))
                      else
                        Prims.raise
                          (FStar_Errors.Error
                             (let _0_630 =
                                FStar_TypeChecker_Err.expected_pure_expression
                                  e c
                                 in
                              (_0_630, (e.FStar_Syntax_Syntax.pos))))))

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
      let uu____8207 = tc_tot_or_gtot_term env t  in
      match uu____8207 with
      | (t,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; (t, c))

let type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      (let uu____8227 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____8227
       then
         let _0_631 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" _0_631
       else ());
      (let env =
         let uu___123_8230 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___123_8230.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___123_8230.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___123_8230.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___123_8230.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___123_8230.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___123_8230.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___123_8230.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___123_8230.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___123_8230.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___123_8230.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___123_8230.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___123_8230.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___123_8230.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___123_8230.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___123_8230.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___123_8230.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___123_8230.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___123_8230.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___123_8230.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___123_8230.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___123_8230.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____8233 =
         try tc_tot_or_gtot_term env e
         with
         | FStar_Errors.Error (msg,uu____8249) ->
             Prims.raise
               (FStar_Errors.Error
                  (let _0_632 = FStar_TypeChecker_Env.get_range env  in
                   ((Prims.strcat "Implicit argument: " msg), _0_632)))
          in
       match uu____8233 with
       | (t,c,g) ->
           let uu____8259 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____8259
           then (t, (c.FStar_Syntax_Syntax.lcomp_res_typ), g)
           else
             Prims.raise
               (FStar_Errors.Error
                  (let _0_635 =
                     let _0_633 = FStar_Syntax_Print.term_to_string e  in
                     FStar_Util.format1
                       "Implicit argument: Expected a total term; got a ghost term: %s"
                       _0_633
                      in
                   let _0_634 = FStar_TypeChecker_Env.get_range env  in
                   (_0_635, _0_634))))
  
let level_of_type_fail env e t =
  Prims.raise
    (FStar_Errors.Error
       (let _0_638 =
          let _0_636 = FStar_Syntax_Print.term_to_string e  in
          FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
            _0_636 t
           in
        let _0_637 = FStar_TypeChecker_Env.get_range env  in (_0_638, _0_637)))
  
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t =
          let uu____8302 =
            (FStar_Syntax_Util.unrefine t).FStar_Syntax_Syntax.n  in
          match uu____8302 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____8304 ->
              if retry
              then
                let t =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t
                   in
                aux false t
              else
                (let uu____8307 = FStar_Syntax_Util.type_u ()  in
                 match uu____8307 with
                 | (t_u,u) ->
                     let env =
                       let uu___126_8313 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___126_8313.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___126_8313.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___126_8313.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___126_8313.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___126_8313.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___126_8313.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___126_8313.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___126_8313.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___126_8313.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___126_8313.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___126_8313.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___126_8313.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___126_8313.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___126_8313.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___126_8313.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___126_8313.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___126_8313.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___126_8313.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___126_8313.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___126_8313.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___126_8313.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___126_8313.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___126_8313.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env t t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let _0_639 = FStar_Syntax_Print.term_to_string t
                              in
                           level_of_type_fail env e _0_639
                       | uu____8317 ->
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
      let uu____8326 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
         in
      match uu____8326 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____8333 ->
          let e = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____8344) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____8369,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____8384) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____8391 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8391 with | (uu____8400,t) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____8402,FStar_Util.Inl t,uu____8404) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____8423,FStar_Util.Inr c,uu____8425) ->
          FStar_TypeChecker_Env.result_typ env c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____8455;
             FStar_Syntax_Syntax.pos = uu____8456;
             FStar_Syntax_Syntax.vars = uu____8457;_},us)
          ->
          let uu____8463 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8463 with
           | (us',t) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_640 = FStar_TypeChecker_Env.get_range env  in
                        ("Unexpected number of universe instantiations",
                          _0_640)))
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____8486 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____8487 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____8495) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____8512 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8512 with
           | (bs,c) ->
               let us =
                 FStar_List.map
                   (fun uu____8523  ->
                      match uu____8523 with
                      | (b,uu____8527) ->
                          let _0_641 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort _0_641)
                   bs
                  in
               let u_res =
                 let res = FStar_TypeChecker_Env.result_typ env c  in
                 let _0_642 = universe_of_aux env res  in
                 level_of_type env res _0_642  in
               let u_c =
                 let uu____8531 = FStar_TypeChecker_Util.effect_repr env c
                    in
                 match uu____8531 with
                 | None  -> u_res
                 | Some trepr ->
                     let _0_643 = universe_of_aux env trepr  in
                     level_of_type env trepr _0_643
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
                -> let _0_644 = universe_of_aux env hd  in (_0_644, args)
            | FStar_Syntax_Syntax.Tm_match (uu____8626,hd::uu____8628) ->
                let uu____8675 = FStar_Syntax_Subst.open_branch hd  in
                (match uu____8675 with
                 | (uu____8685,uu____8686,hd) ->
                     let uu____8702 = FStar_Syntax_Util.head_and_args hd  in
                     (match uu____8702 with
                      | (hd,args) -> type_of_head retry hd args))
            | uu____8737 when retry ->
                let e =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____8739 = FStar_Syntax_Util.head_and_args e  in
                (match uu____8739 with
                 | (hd,args) -> type_of_head false hd args)
            | uu____8774 ->
                let uu____8775 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                (match uu____8775 with
                 | (env,uu____8789) ->
                     let env =
                       let uu___127_8793 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___127_8793.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___127_8793.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___127_8793.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___127_8793.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___127_8793.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___127_8793.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___127_8793.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___127_8793.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___127_8793.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___127_8793.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___127_8793.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___127_8793.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___127_8793.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___127_8793.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___127_8793.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___127_8793.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___127_8793.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___127_8793.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___127_8793.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___127_8793.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___127_8793.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     ((let uu____8795 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____8795
                       then
                         let _0_646 =
                           FStar_Range.string_of_range
                             (FStar_TypeChecker_Env.get_range env)
                            in
                         let _0_645 = FStar_Syntax_Print.term_to_string hd
                            in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           _0_646 _0_645
                       else ());
                      (let uu____8797 = tc_term env hd  in
                       match uu____8797 with
                       | (uu____8810,{
                                       FStar_Syntax_Syntax.lcomp_name =
                                         uu____8811;
                                       FStar_Syntax_Syntax.lcomp_univs =
                                         uu____8812;
                                       FStar_Syntax_Syntax.lcomp_indices =
                                         uu____8813;
                                       FStar_Syntax_Syntax.lcomp_res_typ = t;
                                       FStar_Syntax_Syntax.lcomp_cflags =
                                         uu____8815;
                                       FStar_Syntax_Syntax.lcomp_as_comp =
                                         uu____8816;_},g)
                           ->
                           ((let _0_647 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env g
                                in
                             FStar_All.pipe_right _0_647 Prims.ignore);
                            (t, args)))))
             in
          let uu____8838 = type_of_head true hd args  in
          (match uu____8838 with
           | (t,args) ->
               let t =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____8867 = FStar_Syntax_Util.arrow_formals_comp t  in
               (match uu____8867 with
                | (bs,res) ->
                    let res = FStar_TypeChecker_Env.result_typ env res  in
                    if (FStar_List.length bs) = (FStar_List.length args)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args  in
                      FStar_Syntax_Subst.subst subst res
                    else
                      (let _0_648 = FStar_Syntax_Print.term_to_string res  in
                       level_of_type_fail env e _0_648)))
      | FStar_Syntax_Syntax.Tm_match (uu____8900,hd::uu____8902) ->
          let uu____8949 = FStar_Syntax_Subst.open_branch hd  in
          (match uu____8949 with
           | (uu____8952,uu____8953,hd) -> universe_of_aux env hd)
      | FStar_Syntax_Syntax.Tm_match (uu____8969,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let _0_649 = universe_of_aux env e  in level_of_type env e _0_649
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____9015 = tc_binders env tps  in
      match uu____9015 with
      | (tps,env,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (tps, env, us))
  