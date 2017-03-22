open Prims
let instantiate_both : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___85_4 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___85_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___85_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___85_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___85_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___85_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___85_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___85_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___85_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___85_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___85_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___85_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___85_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___85_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___85_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___85_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___85_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___85_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___85_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___85_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___85_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___85_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___85_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___85_4.FStar_TypeChecker_Env.qname_and_index)
    }
  
let no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___86_8 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___86_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___86_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___86_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___86_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___86_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___86_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___86_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___86_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___86_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___86_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___86_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___86_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___86_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___86_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___86_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___86_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___86_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___86_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___86_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___86_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___86_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___86_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___86_8.FStar_TypeChecker_Env.qname_and_index)
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
  fun uu___79_47  ->
    match uu___79_47 with
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
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___87_181 = lc  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___87_181.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___87_181.FStar_Syntax_Syntax.cflags);
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
                if uu____238
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c)
                     in
                  let uu____240 =
                    let uu____241 = FStar_Syntax_Subst.compress t1  in
                    uu____241.FStar_Syntax_Syntax.n  in
                  (match uu____240 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____245 -> false
                   | uu____246 -> true)
                else false
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
                  if uu____254
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e  in
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
                  if uu____276
                  then
                    let uu____277 = FStar_Syntax_Print.term_to_string t  in
                    let uu____278 = FStar_Syntax_Print.term_to_string t'  in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____277
                      uu____278
                  else ());
                 (let uu____280 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t'
                     in
                  match uu____280 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                      let uu____291 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____291 with
                       | (e2,g) ->
                           ((let uu____300 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____300
                             then
                               let uu____301 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____302 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____303 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____304 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____301 uu____302 uu____303 uu____304
                             else ());
                            (let msg =
                               let uu____310 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               if uu____310
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_28  -> Some _0_28)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             let uu____325 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1
                                in
                             match uu____325 with
                             | (lc2,g2) ->
                                 let uu____333 = memo_tk e2 t'  in
                                 (uu____333, (set_lcomp_result lc2 t'), g2))))))
             in
          match uu____264 with
          | (e1,lc1,g) ->
              ((let uu____341 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                if uu____341
                then
                  let uu____342 = FStar_Syntax_Print.lcomp_to_string lc1  in
                  FStar_Util.print1 "Return comp type is %s\n" uu____342
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
        let uu____359 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____359 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____365 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____365 with
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
                  if uu____403
                  then
                    let uu____406 =
                      FStar_Syntax_Util.ml_comp
                        (FStar_Syntax_Util.comp_result c)
                        e.FStar_Syntax_Syntax.pos
                       in
                    Some uu____406
                  else
                    (let uu____408 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____408
                     then None
                     else
                       (let uu____411 = FStar_Syntax_Util.is_pure_comp c  in
                        if uu____411
                        then
                          let uu____413 =
                            FStar_Syntax_Syntax.mk_Total
                              (FStar_Syntax_Util.comp_result c)
                             in
                          Some uu____413
                        else
                          (let uu____415 =
                             FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                           if uu____415
                           then
                             let uu____417 =
                               FStar_Syntax_Syntax.mk_GTotal
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             Some uu____417
                           else None)))
               in
            (match expected_c_opt with
             | None  ->
                 let uu____422 = norm_c env c  in
                 (e, uu____422, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____425 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                   if uu____425
                   then
                     let uu____426 = FStar_Syntax_Print.term_to_string e  in
                     let uu____427 = FStar_Syntax_Print.comp_to_string c  in
                     let uu____428 =
                       FStar_Syntax_Print.comp_to_string expected_c  in
                     FStar_Util.print3
                       "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                       uu____426 uu____427 uu____428
                   else ());
                  (let c1 = norm_c env c  in
                   (let uu____432 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                    if uu____432
                    then
                      let uu____433 = FStar_Syntax_Print.term_to_string e  in
                      let uu____434 = FStar_Syntax_Print.comp_to_string c1
                         in
                      let uu____435 =
                        FStar_Syntax_Print.comp_to_string expected_c  in
                      FStar_Util.print3
                        "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                        uu____433 uu____434 uu____435
                    else ());
                   (let uu____437 =
                      FStar_TypeChecker_Util.check_comp env e c1 expected_c
                       in
                    match uu____437 with
                    | (e1,uu____445,g) ->
                        let g1 =
                          let uu____448 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_TypeChecker_Util.label_guard uu____448
                            "could not prove post-condition" g
                           in
                        ((let uu____450 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low
                             in
                          if uu____450
                          then
                            let uu____451 =
                              FStar_Range.string_of_range
                                e1.FStar_Syntax_Syntax.pos
                               in
                            let uu____452 =
                              FStar_TypeChecker_Rel.guard_to_string env g1
                               in
                            FStar_Util.print2
                              "(%s) DONE check_expected_effect; guard is: %s\n"
                              uu____451 uu____452
                          else ());
                         (let e2 =
                            FStar_TypeChecker_Util.maybe_lift env e1
                              (FStar_Syntax_Util.comp_effect_name c1)
                              (FStar_Syntax_Util.comp_effect_name expected_c)
                              (FStar_Syntax_Util.comp_result c1)
                             in
                          (e2, expected_c, g1)))))))
  
let no_logical_guard env uu____474 =
  match uu____474 with
  | (te,kt,f) ->
      let uu____481 = FStar_TypeChecker_Rel.guard_form f  in
      (match uu____481 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____486 =
             let uu____487 =
               let uu____490 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
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
  if uu____536
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____537;
          FStar_Syntax_Syntax.effect_name = uu____538;
          FStar_Syntax_Syntax.result_typ = uu____539;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____543)::[];
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
                 "Pattern misses at least one bound variable: %s" uu____604
                in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____603)
    | uu____605 -> failwith "Impossible"
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
        let uu____626 =
          let uu____627 = FStar_TypeChecker_Env.should_verify env  in
          Prims.op_Negation uu____627  in
        if uu____626
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env  in
               let env1 =
                 let uu___88_645 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___88_645.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___88_645.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___88_645.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___88_645.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___88_645.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___88_645.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___88_645.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___88_645.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___88_645.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___88_645.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___88_645.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___88_645.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___88_645.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___88_645.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___88_645.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___88_645.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___88_645.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___88_645.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___88_645.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___88_645.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___88_645.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___88_645.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___88_645.FStar_TypeChecker_Env.qname_and_index)
                 }  in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid
                  in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____668  ->
                           match uu____668 with
                           | (b,uu____673) ->
                               let t =
                                 let uu____675 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort
                                    in
                                 unfold_whnf env1 uu____675  in
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
                   | (head1,uu____696) ->
                       (match head1.FStar_Syntax_Syntax.n with
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
                        (fun uu___80_719  ->
                           match uu___80_719 with
                           | FStar_Syntax_Syntax.DECREASES uu____720 -> true
                           | uu____723 -> false))
                    in
                 match uu____715 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____727 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions  in
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
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____788  ->
                                    match uu____788 with
                                    | (x,imp) ->
                                        let uu____795 =
                                          FStar_Syntax_Syntax.is_null_bv x
                                           in
                                        if uu____795
                                        then
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
                                        else (x, imp)))
                             in
                          let uu____803 =
                            FStar_Syntax_Subst.open_comp formals1 c  in
                          (match uu____803 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1  in
                               let precedes1 =
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
                               let uu____826 = FStar_Util.prefix formals2  in
                               (match uu____826 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___89_852 = last1  in
                                      let uu____853 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___89_852.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___89_852.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____853
                                      }  in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)]  in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1
                                       in
                                    ((let uu____870 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low
                                         in
                                      if uu____870
                                      then
                                        let uu____871 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l
                                           in
                                        let uu____872 =
                                          FStar_Syntax_Print.term_to_string t
                                           in
                                        let uu____873 =
                                          FStar_Syntax_Print.term_to_string
                                            t'
                                           in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____871 uu____872 uu____873
                                      else ());
                                     (l, t'))))
                      | uu____877 ->
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
        (let uu___90_1141 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___90_1141.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___90_1141.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___90_1141.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___90_1141.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___90_1141.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___90_1141.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___90_1141.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___90_1141.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___90_1141.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___90_1141.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___90_1141.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___90_1141.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___90_1141.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___90_1141.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___90_1141.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___90_1141.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___90_1141.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___90_1141.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___90_1141.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___90_1141.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___90_1141.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___90_1141.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___90_1141.FStar_TypeChecker_Env.qname_and_index)
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
      (let uu____1150 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____1150
       then
         let uu____1151 =
           let uu____1152 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1152  in
         let uu____1153 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____1151 uu____1153
       else ());
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
           -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1198 = tc_tot_or_gtot_term env1 e1  in
           (match uu____1198 with
            | (e2,c,g) ->
                let g1 =
                  let uu___91_1209 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___91_1209.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___91_1209.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___91_1209.FStar_TypeChecker_Env.implicits)
                  }  in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1222 = FStar_Syntax_Util.type_u ()  in
           (match uu____1222 with
            | (t,u) ->
                let uu____1230 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____1230 with
                 | (e2,c,g) ->
                     let uu____1240 =
                       let uu____1249 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____1249 with
                       | (env2,uu____1262) -> tc_pats env2 pats  in
                     (match uu____1240 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___92_1283 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___92_1283.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___92_1283.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___92_1283.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____1284 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____1295 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____1284, c, uu____1295))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1303 =
             let uu____1304 = FStar_Syntax_Subst.compress e1  in
             uu____1304.FStar_Syntax_Syntax.n  in
           (match uu____1303 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1310,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1312;
                               FStar_Syntax_Syntax.lbtyp = uu____1313;
                               FStar_Syntax_Syntax.lbeff = uu____1314;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1332 =
                  let uu____1336 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit
                     in
                  tc_term uu____1336 e11  in
                (match uu____1332 with
                 | (e12,c1,g1) ->
                     let uu____1343 = tc_term env1 e2  in
                     (match uu____1343 with
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
                                            e13)
                                         in
                                      [uu____1378]  in
                                    (false, uu____1376)  in
                                  (uu____1372, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____1364  in
                              FStar_Syntax_Syntax.mk uu____1363  in
                            uu____1360
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
                          let uu____1408 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e5, c, uu____1408)))
            | uu____1411 ->
                let uu____1412 = tc_term env1 e1  in
                (match uu____1412 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1436) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1451 = tc_term env1 e1  in
           (match uu____1451 with
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
           (e1,FStar_Util.Inr expected_c,uu____1476) ->
           let uu____1495 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____1495 with
            | (env0,uu____1503) ->
                let uu____1506 = tc_comp env0 expected_c  in
                (match uu____1506 with
                 | (expected_c1,uu____1514,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1
                        in
                     let uu____1519 =
                       let uu____1523 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____1523 e1  in
                     (match uu____1519 with
                      | (e2,c',g') ->
                          let uu____1530 =
                            let uu____1534 =
                              let uu____1537 = c'.FStar_Syntax_Syntax.comp ()
                                 in
                              (e2, uu____1537)  in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1534
                             in
                          (match uu____1530 with
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
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2
                                  in
                               let f =
                                 let uu____1572 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1572
                                  in
                               let uu____1573 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____1573 with
                                | (e5,c,f2) ->
                                    let uu____1583 =
                                      FStar_TypeChecker_Rel.conj_guard f f2
                                       in
                                    (e5, c, uu____1583))))))
       | FStar_Syntax_Syntax.Tm_ascribed (e1,FStar_Util.Inl t,uu____1586) ->
           let uu____1605 = FStar_Syntax_Util.type_u ()  in
           (match uu____1605 with
            | (k,u) ->
                let uu____1613 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____1613 with
                 | (t1,uu____1621,f) ->
                     let uu____1623 =
                       let uu____1627 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____1627 e1  in
                     (match uu____1623 with
                      | (e2,c,g) ->
                          let uu____1634 =
                            let uu____1637 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1640  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1637 e2 c f
                             in
                          (match uu____1634 with
                           | (c1,f1) ->
                               let uu____1646 =
                                 let uu____1650 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, (FStar_Util.Inl t1),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env1 uu____1650 c1
                                  in
                               (match uu____1646 with
                                | (e3,c2,f2) ->
                                    let uu____1672 =
                                      let uu____1673 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1673
                                       in
                                    (e3, c2, uu____1672))))))
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
           let uu____1750 = FStar_Syntax_Util.head_and_args top  in
           (match uu____1750 with
            | (unary_op,uu____1764) ->
                let head1 =
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
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1826;
              FStar_Syntax_Syntax.pos = uu____1827;
              FStar_Syntax_Syntax.vars = uu____1828;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____1854 =
               let uu____1858 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               match uu____1858 with | (env0,uu____1866) -> tc_term env0 e1
                in
             match uu____1854 with
             | (e2,c,g) ->
                 let uu____1875 = FStar_Syntax_Util.head_and_args top  in
                 (match uu____1875 with
                  | (reify_op,uu____1889) ->
                      let u_c =
                        let uu____1905 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ  in
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
                                        FStar_TypeChecker_Rel.try_teq env1
                                          c'.FStar_Syntax_Syntax.res_typ t
                                         in
                                      ((match g_opt with
                                        | Some g' ->
                                            FStar_TypeChecker_Rel.force_trivial_guard
                                              env1 g'
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
                      let repr =
                        let uu____1932 = c.FStar_Syntax_Syntax.comp ()  in
                        FStar_TypeChecker_Env.reify_comp env1 uu____1932 u_c
                         in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos
                         in
                      let c1 =
                        let uu____1954 = FStar_Syntax_Syntax.mk_Total repr
                           in
                        FStar_All.pipe_right uu____1954
                          FStar_Syntax_Util.lcomp_of_comp
                         in
                      let uu____1955 = comp_check_expected_typ env1 e3 c1  in
                      (match uu____1955 with
                       | (e4,c2,g') ->
                           let uu____1965 =
                             FStar_TypeChecker_Rel.conj_guard g g'  in
                           (e4, c2, uu____1965)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____1967;
              FStar_Syntax_Syntax.pos = uu____1968;
              FStar_Syntax_Syntax.vars = uu____1969;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2001 =
               let uu____2002 =
                 let uu____2003 =
                   let uu____2006 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str
                      in
                   (uu____2006, (e1.FStar_Syntax_Syntax.pos))  in
                 FStar_Errors.Error uu____2003  in
               Prims.raise uu____2002  in
             let uu____2010 = FStar_Syntax_Util.head_and_args top  in
             match uu____2010 with
             | (reflect_op,uu____2024) ->
                 let uu____2039 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____2039 with
                  | None  -> no_reflect ()
                  | Some ed ->
                      let uu____2045 =
                        let uu____2046 =
                          FStar_All.pipe_right
                            ed.FStar_Syntax_Syntax.qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____2046  in
                      if uu____2045
                      then no_reflect ()
                      else
                        (let uu____2052 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____2052 with
                         | (env_no_ex,topt) ->
                             let uu____2063 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____2078 =
                                   let uu____2081 =
                                     let uu____2082 =
                                       let uu____2092 =
                                         let uu____2094 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____2095 =
                                           let uu____2097 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____2097]  in
                                         uu____2094 :: uu____2095  in
                                       (repr, uu____2092)  in
                                     FStar_Syntax_Syntax.Tm_app uu____2082
                                      in
                                   FStar_Syntax_Syntax.mk uu____2081  in
                                 uu____2078 None top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____2107 =
                                 let uu____2111 =
                                   let uu____2112 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____2112 Prims.fst
                                    in
                                 tc_tot_or_gtot_term uu____2111 t  in
                               match uu____2107 with
                               | (t1,uu____2129,g) ->
                                   let uu____2131 =
                                     let uu____2132 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____2132.FStar_Syntax_Syntax.n  in
                                   (match uu____2131 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2143,(res,uu____2145)::
                                         (wp,uu____2147)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2181 -> failwith "Impossible")
                                in
                             (match uu____2063 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2205 =
                                    let uu____2208 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____2208 with
                                    | (e2,c,g) ->
                                        ((let uu____2218 =
                                            let uu____2219 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2219
                                             in
                                          if uu____2218
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2225 =
                                            FStar_TypeChecker_Rel.try_teq
                                              env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____2225 with
                                          | None  ->
                                              ((let uu____2230 =
                                                  let uu____2234 =
                                                    let uu____2237 =
                                                      let uu____2238 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____2239 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2238 uu____2239
                                                       in
                                                    (uu____2237,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____2234]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2230);
                                               (let uu____2244 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____2244)))
                                          | Some g' ->
                                              let uu____2246 =
                                                let uu____2247 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2247
                                                 in
                                              (e2, uu____2246)))
                                     in
                                  (match uu____2205 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2254 =
                                           let uu____2255 =
                                             let uu____2256 =
                                               let uu____2257 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____2257]  in
                                             let uu____2258 =
                                               let uu____2264 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____2264]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2256;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2258;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2255
                                            in
                                         FStar_All.pipe_right uu____2254
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
                                       let uu____2285 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____2285 with
                                        | (e4,c1,g') ->
                                            let uu____2295 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____2295))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____2314 =
               let uu____2315 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____2315 Prims.fst  in
             FStar_All.pipe_right uu____2314 instantiate_both  in
           ((let uu____2324 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____2324
             then
               let uu____2325 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____2326 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2325
                 uu____2326
             else ());
            (let uu____2328 = tc_term (no_inst env2) head1  in
             match uu____2328 with
             | (head2,chead,g_head) ->
                 let uu____2338 =
                   let uu____2342 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____2342
                   then
                     let uu____2346 = FStar_TypeChecker_Env.expected_typ env0
                        in
                     check_short_circuit_args env2 head2 chead g_head args
                       uu____2346
                   else
                     (let uu____2349 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____2349)
                    in
                 (match uu____2338 with
                  | (e1,c,g) ->
                      ((let uu____2358 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____2358
                        then
                          let uu____2359 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2359
                        else ());
                       (let c1 =
                          let uu____2362 =
                            ((FStar_TypeChecker_Env.should_verify env2) &&
                               (let uu____2363 =
                                  FStar_Syntax_Util.is_lcomp_partial_return c
                                   in
                                Prims.op_Negation uu____2363))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                             in
                          if uu____2362
                          then
                            FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                              env2 e1 c
                          else c  in
                        let uu____2365 = comp_check_expected_typ env0 e1 c1
                           in
                        match uu____2365 with
                        | (e2,c2,g') ->
                            let gimp =
                              let uu____2376 =
                                let uu____2377 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____2377.FStar_Syntax_Syntax.n  in
                              match uu____2376 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2381) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c2.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___93_2413 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___93_2413.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___93_2413.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___93_2413.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2438 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____2440 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____2440
                               in
                            ((let uu____2442 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____2442
                              then
                                let uu____2443 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____2444 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2443 uu____2444
                              else ());
                             (e2, c2, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2474 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____2474 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____2486 = tc_term env12 e1  in
                (match uu____2486 with
                 | (e11,c1,g1) ->
                     let uu____2496 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2502 = FStar_Syntax_Util.type_u ()  in
                           (match uu____2502 with
                            | (k,uu____2508) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k  in
                                let uu____2510 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t
                                   in
                                (uu____2510, res_t))
                        in
                     (match uu____2496 with
                      | (env_branches,res_t) ->
                          ((let uu____2517 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____2517
                            then
                              let uu____2518 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2518
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
                            let uu____2569 =
                              let uu____2572 =
                                FStar_List.fold_right
                                  (fun uu____2591  ->
                                     fun uu____2592  ->
                                       match (uu____2591, uu____2592) with
                                       | ((uu____2624,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2657 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), uu____2657))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____2572 with
                              | (cases,g) ->
                                  let uu____2678 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____2678, g)
                               in
                            match uu____2569 with
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
                                           (fun uu____2731  ->
                                              match uu____2731 with
                                              | ((pat,wopt,br),uu____2747,lc,uu____2749)
                                                  ->
                                                  let uu____2756 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  (pat, wopt, uu____2756)))
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
                                            (FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.eff_name)))))
                                      None e3.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____2796 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____2796
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____2803 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____2803  in
                                     let lb =
                                       let uu____2807 =
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
                                           uu____2807;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       }  in
                                     let e2 =
                                       let uu____2811 =
                                         let uu____2814 =
                                           let uu____2815 =
                                             let uu____2823 =
                                               let uu____2824 =
                                                 let uu____2825 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____2825]  in
                                               FStar_Syntax_Subst.close
                                                 uu____2824 e_match
                                                in
                                             ((false, [lb]), uu____2823)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____2815
                                            in
                                         FStar_Syntax_Syntax.mk uu____2814
                                          in
                                       uu____2811
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____2839 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____2839
                                  then
                                    let uu____2840 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____2841 =
                                      let uu____2842 =
                                        cres.FStar_Syntax_Syntax.comp ()  in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____2842
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____2840 uu____2841
                                  else ());
                                 (let uu____2844 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e2, cres, uu____2844))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2847;
                FStar_Syntax_Syntax.lbunivs = uu____2848;
                FStar_Syntax_Syntax.lbtyp = uu____2849;
                FStar_Syntax_Syntax.lbeff = uu____2850;
                FStar_Syntax_Syntax.lbdef = uu____2851;_}::[]),uu____2852)
           ->
           ((let uu____2867 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____2867
             then
               let uu____2868 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____2868
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2870),uu____2871) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2881;
                FStar_Syntax_Syntax.lbunivs = uu____2882;
                FStar_Syntax_Syntax.lbtyp = uu____2883;
                FStar_Syntax_Syntax.lbeff = uu____2884;
                FStar_Syntax_Syntax.lbdef = uu____2885;_}::uu____2886),uu____2887)
           ->
           ((let uu____2903 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____2903
             then
               let uu____2904 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____2904
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____2906),uu____2907) ->
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
        let uu____2951 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____2951 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____2964 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____2964
              then FStar_Util.Inl t1
              else
                (let uu____2968 =
                   let uu____2969 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____2969
                    in
                 FStar_Util.Inr uu____2968)
               in
            let is_data_ctor uu___81_2978 =
              match uu___81_2978 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____2981 -> false  in
            let uu____2983 =
              (is_data_ctor dc) &&
                (let uu____2984 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____2984)
               in
            if uu____2983
            then
              let uu____2990 =
                let uu____2991 =
                  let uu____2994 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  let uu____2997 = FStar_TypeChecker_Env.get_range env1  in
                  (uu____2994, uu____2997)  in
                FStar_Errors.Error uu____2991  in
              Prims.raise uu____2990
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3008 =
            let uu____3009 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3009
             in
          failwith uu____3008
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3028 =
              let uu____3029 = FStar_Syntax_Subst.compress t1  in
              uu____3029.FStar_Syntax_Syntax.n  in
            match uu____3028 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3032 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3040 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___94_3060 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___94_3060.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___94_3060.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___94_3060.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____3088 =
            let uu____3095 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____3095 with
            | None  ->
                let uu____3103 = FStar_Syntax_Util.type_u ()  in
                (match uu____3103 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard)  in
          (match uu____3088 with
           | (t,uu____3124,g0) ->
               let uu____3132 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____3132 with
                | (e1,uu____3143,g1) ->
                    let uu____3151 =
                      let uu____3152 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____3152
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____3153 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____3151, uu____3153)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let t =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then x.FStar_Syntax_Syntax.sort
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          let x1 =
            let uu___95_3162 = x  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___95_3162.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___95_3162.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = t
            }  in
          (FStar_TypeChecker_Common.insert_bv x1 t;
           (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
            let uu____3165 =
              FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
            match uu____3165 with
            | (e2,t1,implicits) ->
                let tc =
                  let uu____3178 = FStar_TypeChecker_Env.should_verify env1
                     in
                  if uu____3178
                  then FStar_Util.Inl t1
                  else
                    (let uu____3182 =
                       let uu____3183 = FStar_Syntax_Syntax.mk_Total t1  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3183
                        in
                     FStar_Util.Inr uu____3182)
                   in
                value_check_expected_typ env1 e2 tc implicits))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3189;
             FStar_Syntax_Syntax.pos = uu____3190;
             FStar_Syntax_Syntax.vars = uu____3191;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____3199 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3199 with
           | (us',t) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3216 =
                     let uu____3217 =
                       let uu____3220 = FStar_TypeChecker_Env.get_range env1
                          in
                       ("Unexpected number of universe instantiations",
                         uu____3220)
                        in
                     FStar_Errors.Error uu____3217  in
                   Prims.raise uu____3216)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____3228 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___96_3230 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___97_3231 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___97_3231.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___97_3231.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___96_3230.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___96_3230.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____3246 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3246 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3258 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3258 with
           | (us,t) ->
               ((let uu____3271 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____3271
                 then
                   let uu____3272 =
                     let uu____3273 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____3273  in
                   let uu____3274 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3275 =
                     let uu____3276 =
                       let uu____3277 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.range_of_lid uu____3277  in
                     FStar_Range.string_of_range uu____3276  in
                   let uu____3278 =
                     let uu____3279 =
                       let uu____3280 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.range_of_lid uu____3280  in
                     FStar_Range.string_of_use_range uu____3279  in
                   let uu____3281 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s"
                     uu____3272 uu____3274 uu____3275 uu____3278 uu____3281
                 else ());
                (let fv' =
                   let uu___98_3284 = fv  in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___99_3285 = fv.FStar_Syntax_Syntax.fv_name  in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___99_3285.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___99_3285.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___98_3284.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___98_3284.FStar_Syntax_Syntax.fv_qual)
                   }  in
                 FStar_TypeChecker_Common.insert_fv fv t;
                 (let e1 =
                    let uu____3300 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3300 us  in
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
          let uu____3336 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3336 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____3345 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____3345 with
                | (env2,uu____3353) ->
                    let uu____3356 = tc_binders env2 bs1  in
                    (match uu____3356 with
                     | (bs2,env3,g,us) ->
                         let uu____3368 = tc_comp env3 c1  in
                         (match uu____3368 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___100_3381 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___100_3381.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___100_3381.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___100_3381.FStar_Syntax_Syntax.vars)
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
                                  let uu____3402 =
                                    FStar_TypeChecker_Rel.close_guard bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3402
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
          let uu____3437 =
            let uu____3440 =
              let uu____3441 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____3441]  in
            FStar_Syntax_Subst.open_term uu____3440 phi  in
          (match uu____3437 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____3448 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____3448 with
                | (env2,uu____3456) ->
                    let uu____3459 =
                      let uu____3466 = FStar_List.hd x1  in
                      tc_binder env2 uu____3466  in
                    (match uu____3459 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3483 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____3483
                           then
                             let uu____3484 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____3485 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____3486 =
                               FStar_Syntax_Print.bv_to_string (Prims.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3484 uu____3485 uu____3486
                           else ());
                          (let uu____3488 = FStar_Syntax_Util.type_u ()  in
                           match uu____3488 with
                           | (t_phi,uu____3495) ->
                               let uu____3496 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____3496 with
                                | (phi2,uu____3504,f2) ->
                                    let e1 =
                                      let uu___101_3509 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x2) phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___101_3509.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___101_3509.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___101_3509.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____3528 =
                                        FStar_TypeChecker_Rel.close_guard
                                          [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3528
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3537) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____3562 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____3562
            then
              let uu____3563 =
                FStar_Syntax_Print.term_to_string
                  (let uu___102_3564 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___102_3564.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___102_3564.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___102_3564.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3563
            else ());
           (let uu____3583 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____3583 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3591 ->
          let uu____3592 =
            let uu____3593 = FStar_Syntax_Print.term_to_string top  in
            let uu____3594 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3593
              uu____3594
             in
          failwith uu____3592

and tc_constant :
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3600 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3601,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3607,Some uu____3608) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3616 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3620 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3621 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3622 ->
          FStar_TypeChecker_Common.t_range
      | uu____3623 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____3634) ->
          let uu____3641 = FStar_Syntax_Util.type_u ()  in
          (match uu____3641 with
           | (k,u) ->
               let uu____3649 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3649 with
                | (t1,uu____3657,g) ->
                    let uu____3659 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u)  in
                    (uu____3659, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3661) ->
          let uu____3668 = FStar_Syntax_Util.type_u ()  in
          (match uu____3668 with
           | (k,u) ->
               let uu____3676 = tc_check_tot_or_gtot_term env t k  in
               (match uu____3676 with
                | (t1,uu____3684,g) ->
                    let uu____3686 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u)  in
                    (uu____3686, u, g)))
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
            let uu____3702 =
              let uu____3703 =
                let uu____3704 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____3704 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____3703  in
            uu____3702 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____3709 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____3709 with
           | (tc1,uu____3717,f) ->
               let uu____3719 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____3719 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____3749 =
                        let uu____3750 = FStar_Syntax_Subst.compress head3
                           in
                        uu____3750.FStar_Syntax_Syntax.n  in
                      match uu____3749 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3753,us) -> us
                      | uu____3759 -> []  in
                    let uu____3760 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____3760 with
                     | (uu____3773,args1) ->
                         let uu____3789 =
                           let uu____3801 = FStar_List.hd args1  in
                           let uu____3810 = FStar_List.tl args1  in
                           (uu____3801, uu____3810)  in
                         (match uu____3789 with
                          | (res,args2) ->
                              let uu____3852 =
                                let uu____3857 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___82_3867  ->
                                          match uu___82_3867 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____3873 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____3873 with
                                               | (env1,uu____3880) ->
                                                   let uu____3883 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____3883 with
                                                    | (e1,uu____3890,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____3857
                                  FStar_List.unzip
                                 in
                              (match uu____3852 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (Prims.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___103_3913 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___103_3913.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (Prims.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___103_3913.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____3917 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____3917 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____3920 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____3920))))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____3928 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3931 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3931
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3934 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3934
        | FStar_Syntax_Syntax.U_name x -> u2  in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____3938 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____3938 Prims.snd
         | uu____3943 -> aux u)

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
            let uu____3964 =
              let uu____3965 =
                let uu____3968 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top
                   in
                (uu____3968, (top.FStar_Syntax_Syntax.pos))  in
              FStar_Errors.Error uu____3965  in
            Prims.raise uu____3964  in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4022 bs2 bs_expected1 =
              match uu____4022 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             let uu____4119 =
                               let uu____4120 =
                                 let uu____4123 =
                                   let uu____4124 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4124
                                    in
                                 let uu____4125 =
                                   FStar_Syntax_Syntax.range_of_bv hd1  in
                                 (uu____4123, uu____4125)  in
                               FStar_Errors.Error uu____4120  in
                             Prims.raise uu____4119
                         | uu____4126 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____4130 =
                           let uu____4133 =
                             let uu____4134 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____4134.FStar_Syntax_Syntax.n  in
                           match uu____4133 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4139 ->
                               ((let uu____4141 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____4141
                                 then
                                   let uu____4142 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4142
                                 else ());
                                (let uu____4144 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____4144 with
                                 | (t,uu____4151,g1) ->
                                     let g2 =
                                       let uu____4154 =
                                         FStar_TypeChecker_Env.get_range env2
                                          in
                                       let uu____4155 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t
                                          in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4154
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4155
                                        in
                                     let g3 =
                                       let uu____4157 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4157
                                        in
                                     (t, g3)))
                            in
                         match uu____4130 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___104_4173 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___104_4173.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___104_4173.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____4182 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____4182
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
                  | uu____4278 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4282 = tc_binders env1 bs  in
                  match uu____4282 with
                  | (bs1,envbody,g,uu____4301) ->
                      let uu____4302 =
                        let uu____4307 =
                          let uu____4308 = FStar_Syntax_Subst.compress body1
                             in
                          uu____4308.FStar_Syntax_Syntax.n  in
                        match uu____4307 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,FStar_Util.Inr c,uu____4317) ->
                            let uu____4336 = tc_comp envbody c  in
                            (match uu____4336 with
                             | (c1,uu____4345,g') ->
                                 let uu____4347 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((Some c1), body1, uu____4347))
                        | uu____4349 -> (None, body1, g)  in
                      (match uu____4302 with
                       | (copt,body2,g1) ->
                           (None, bs1, [], copt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____4399 =
                    let uu____4400 = FStar_Syntax_Subst.compress t2  in
                    uu____4400.FStar_Syntax_Syntax.n  in
                  match uu____4399 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4431 -> failwith "Impossible");
                       (let uu____4435 = tc_binders env1 bs  in
                        match uu____4435 with
                        | (bs1,envbody,g,uu____4455) ->
                            let uu____4456 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____4456 with
                             | (envbody1,uu____4473) ->
                                 ((Some (t2, true)), bs1, [], None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4484) ->
                      let uu____4489 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____4489 with
                       | (uu____4514,bs1,bs',copt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, env2, body2,
                             g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4550 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____4550 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____4611 c_expected2 =
                               match uu____4611 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____4672 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____4672)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____4689 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____4689
                                           in
                                        let uu____4690 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____4690)
                                    | Some (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        if FStar_Syntax_Util.is_named_tot c
                                        then
                                          let t3 =
                                            unfold_whnf env3
                                              (FStar_Syntax_Util.comp_result
                                                 c)
                                             in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____4731 =
                                                 check_binders env3 more_bs
                                                   bs_expected3
                                                  in
                                               (match uu____4731 with
                                                | (env4,bs',more1,guard',subst2)
                                                    ->
                                                    let uu____4758 =
                                                      let uu____4774 =
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          guard guard'
                                                         in
                                                      (env4,
                                                        (FStar_List.append
                                                           bs2 bs'), more1,
                                                        uu____4774, subst2)
                                                       in
                                                    handle_more uu____4758
                                                      c_expected3)
                                           | uu____4783 ->
                                               let uu____4784 =
                                                 let uu____4785 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3
                                                    in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____4785
                                                  in
                                               fail uu____4784 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2)
                                in
                             let uu____4801 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____4801 c_expected1  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___105_4839 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___105_4839.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___105_4839.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___105_4839.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___105_4839.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___105_4839.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___105_4839.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___105_4839.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___105_4839.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___105_4839.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___105_4839.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___105_4839.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___105_4839.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___105_4839.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___105_4839.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___105_4839.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___105_4839.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___105_4839.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___105_4839.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___105_4839.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___105_4839.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___105_4839.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___105_4839.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___105_4839.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____4853  ->
                                     fun uu____4854  ->
                                       match (uu____4853, uu____4854) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____4879 =
                                             let uu____4883 =
                                               let uu____4884 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4884 Prims.fst
                                                in
                                             tc_term uu____4883 t3  in
                                           (match uu____4879 with
                                            | (t4,uu____4896,uu____4897) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____4904 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___106_4905
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___106_4905.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___106_4905.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____4904 ::
                                                        letrec_binders
                                                  | uu____4906 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____4909 =
                             check_actuals_against_formals env1 bs
                               bs_expected1
                              in
                           (match uu____4909 with
                            | (envbody,bs1,g,c) ->
                                let uu____4939 =
                                  let uu____4943 =
                                    FStar_TypeChecker_Env.should_verify env1
                                     in
                                  if uu____4943
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, [])  in
                                (match uu____4939 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), envbody2, body1, g))))
                  | uu____4976 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____4989 = unfold_whnf env1 t2  in
                        as_function_typ true uu____4989
                      else
                        (let uu____4991 =
                           expected_function_typ1 env1 None body1  in
                         match uu____4991 with
                         | (uu____5015,bs1,uu____5017,c_opt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, envbody,
                               body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____5038 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____5038 with
          | (env1,topt) ->
              ((let uu____5050 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____5050
                then
                  let uu____5051 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5051
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5055 = expected_function_typ1 env1 topt body  in
                match uu____5055 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____5085 =
                      tc_term
                        (let uu___107_5089 = envbody  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___107_5089.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___107_5089.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___107_5089.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___107_5089.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___107_5089.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___107_5089.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___107_5089.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___107_5089.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___107_5089.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___107_5089.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___107_5089.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___107_5089.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___107_5089.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___107_5089.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___107_5089.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___107_5089.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___107_5089.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___107_5089.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___107_5089.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___107_5089.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___107_5089.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___107_5089.FStar_TypeChecker_Env.qname_and_index)
                         }) body1
                       in
                    (match uu____5085 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         ((let uu____5098 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits")
                              in
                           if uu____5098
                           then
                             let uu____5099 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits)
                                in
                             let uu____5108 =
                               let uu____5109 =
                                 cbody.FStar_Syntax_Syntax.comp ()  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5109
                                in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5099 uu____5108
                           else ());
                          (let uu____5111 =
                             let uu____5115 =
                               let uu____5118 =
                                 cbody.FStar_Syntax_Syntax.comp ()  in
                               (body2, uu____5118)  in
                             check_expected_effect
                               (let uu___108_5123 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___108_5123.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___108_5123.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___108_5123.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___108_5123.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___108_5123.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___108_5123.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___108_5123.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___108_5123.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___108_5123.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___108_5123.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___108_5123.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___108_5123.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___108_5123.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___108_5123.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___108_5123.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___108_5123.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___108_5123.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___108_5123.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___108_5123.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___108_5123.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___108_5123.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___108_5123.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___108_5123.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5115
                              in
                           match uu____5111 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard
                                  in
                               let guard2 =
                                 let uu____5132 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5133 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1
                                         in
                                      Prims.op_Negation uu____5133)
                                    in
                                 if uu____5132
                                 then
                                   let uu____5134 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1
                                      in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5134
                                 else
                                   (let guard2 =
                                      let uu____5137 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1
                                         in
                                      FStar_TypeChecker_Rel.close_guard
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5137
                                       in
                                    guard2)
                                  in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1  in
                               let e =
                                 let uu____5144 =
                                   let uu____5151 =
                                     let uu____5157 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     FStar_All.pipe_right uu____5157
                                       (fun _0_29  -> FStar_Util.Inl _0_29)
                                      in
                                   Some uu____5151  in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5144
                                  in
                               let uu____5171 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t
                                        in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5186 -> (e, t1, guard2)
                                      | uu____5194 ->
                                          let uu____5195 =
                                            if use_teq
                                            then
                                              let uu____5200 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed
                                                 in
                                              (e, uu____5200)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1
                                             in
                                          (match uu____5195 with
                                           | (e1,guard') ->
                                               let uu____5207 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard'
                                                  in
                                               (e1, t1, uu____5207)))
                                 | None  -> (e, tfun_computed, guard2)  in
                               (match uu____5171 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1
                                       in
                                    let uu____5220 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3
                                       in
                                    (match uu____5220 with
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
              let thead = chead.FStar_Syntax_Syntax.res_typ  in
              (let uu____5256 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____5256
               then
                 let uu____5257 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____5258 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5257
                   uu____5258
               else ());
              (let monadic_application uu____5300 subst1 arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____5300 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres1 =
                       let uu___109_5341 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___109_5341.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___109_5341.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___109_5341.FStar_Syntax_Syntax.comp)
                       }  in
                     let uu____5342 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1
                              in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard
                              in
                           let refine_with_equality =
                             (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
                               &&
                               (FStar_All.pipe_right arg_comps_rev
                                  (FStar_Util.for_some
                                     (fun uu___83_5369  ->
                                        match uu___83_5369 with
                                        | (uu____5378,uu____5379,FStar_Util.Inl
                                           uu____5380) -> false
                                        | (uu____5391,uu____5392,FStar_Util.Inr
                                           c) ->
                                            let uu____5402 =
                                              FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                c
                                               in
                                            Prims.op_Negation uu____5402)))
                              in
                           let cres3 =
                             if refine_with_equality
                             then
                               let uu____5404 =
                                 (FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets))
                                   (Some
                                      ((cres2.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                   r
                                  in
                               FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                 env uu____5404 cres2
                             else
                               ((let uu____5415 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____5415
                                 then
                                   let uu____5416 =
                                     FStar_Syntax_Print.term_to_string head2
                                      in
                                   let uu____5417 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   let uu____5418 =
                                     FStar_TypeChecker_Rel.guard_to_string
                                       env g
                                      in
                                   FStar_Util.print3
                                     "Not refining result: f=%s; cres=%s; guard=%s\n"
                                     uu____5416 uu____5417 uu____5418
                                 else ());
                                cres2)
                              in
                           (cres3, g)
                       | uu____5420 ->
                           let g =
                             let uu____5425 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard
                                in
                             FStar_All.pipe_right uu____5425
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____5426 =
                             let uu____5427 =
                               let uu____5430 =
                                 let uu____5431 =
                                   let uu____5432 =
                                     cres1.FStar_Syntax_Syntax.comp ()  in
                                   FStar_Syntax_Util.arrow bs uu____5432  in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5431
                                  in
                               FStar_Syntax_Syntax.mk_Total uu____5430  in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5427
                              in
                           (uu____5426, g)
                        in
                     (match uu____5342 with
                      | (cres2,guard1) ->
                          ((let uu____5443 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____5443
                            then
                              let uu____5444 =
                                FStar_Syntax_Print.lcomp_to_string cres2  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5444
                            else ());
                           (let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____5460  ->
                                     match uu____5460 with
                                     | ((e,q),x,c) ->
                                         (match c with
                                          | FStar_Util.Inl (eff_name,arg_typ)
                                              -> out_c
                                          | FStar_Util.Inr c1 ->
                                              FStar_TypeChecker_Util.bind
                                                e.FStar_Syntax_Syntax.pos env
                                                None c1 (x, out_c))) cres2
                                arg_comps_rev
                               in
                            let comp1 =
                              FStar_TypeChecker_Util.bind
                                head2.FStar_Syntax_Syntax.pos env None chead1
                                (None, comp)
                               in
                            let shortcuts_evaluation_order =
                              let uu____5506 =
                                let uu____5507 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____5507.FStar_Syntax_Syntax.n  in
                              match uu____5506 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____5511 -> false  in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____5525  ->
                                         match uu____5525 with
                                         | (arg,uu____5537,uu____5538) -> arg
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
                                    cres2.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_TypeChecker_Util.maybe_monadic env app1
                                  comp1.FStar_Syntax_Syntax.eff_name
                                  comp1.FStar_Syntax_Syntax.res_typ
                              else
                                (let uu____5558 =
                                   let map_fun uu____5597 =
                                     match uu____5597 with
                                     | ((e,q),uu____5621,c0) ->
                                         (match c0 with
                                          | FStar_Util.Inl uu____5646 ->
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
                                              let e1 =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env e
                                                  c.FStar_Syntax_Syntax.eff_name
                                                  comp1.FStar_Syntax_Syntax.eff_name
                                                  c.FStar_Syntax_Syntax.res_typ
                                                 in
                                              let uu____5689 =
                                                let uu____5692 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x
                                                   in
                                                (uu____5692, q)  in
                                              ((Some
                                                  (x,
                                                    (c.FStar_Syntax_Syntax.eff_name),
                                                    (c.FStar_Syntax_Syntax.res_typ),
                                                    e1)), uu____5689))
                                      in
                                   let uu____5710 =
                                     let uu____5724 =
                                       let uu____5737 =
                                         let uu____5749 =
                                           let uu____5758 =
                                             FStar_Syntax_Syntax.as_arg head2
                                              in
                                           (uu____5758, None,
                                             (FStar_Util.Inr chead1))
                                            in
                                         uu____5749 :: arg_comps_rev  in
                                       FStar_List.map map_fun uu____5737  in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____5724
                                      in
                                   match uu____5710 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____5867 =
                                         let uu____5868 =
                                           FStar_List.hd reverse_args  in
                                         Prims.fst uu____5868  in
                                       let uu____5873 =
                                         let uu____5877 =
                                           FStar_List.tl reverse_args  in
                                         FStar_List.rev uu____5877  in
                                       (lifted_args, uu____5867, uu____5873)
                                    in
                                 match uu____5558 with
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
                                         cres2.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ
                                        in
                                     let app2 =
                                       FStar_TypeChecker_Util.maybe_monadic
                                         env app1
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ
                                        in
                                     let bind_lifted_args e uu___84_5945 =
                                       match uu___84_5945 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1
                                              in
                                           let letbinding =
                                             let uu____5987 =
                                               let uu____5990 =
                                                 let uu____5991 =
                                                   let uu____5999 =
                                                     let uu____6000 =
                                                       let uu____6001 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____6001]  in
                                                     FStar_Syntax_Subst.close
                                                       uu____6000 e
                                                      in
                                                   ((false, [lb]),
                                                     uu____5999)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____5991
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____5990
                                                in
                                             uu____5987 None
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
                            let uu____6035 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1
                               in
                            match uu____6035 with
                            | (comp2,g) -> (app, comp2, g))))
                  in
               let rec tc_args head_info uu____6093 bs args1 =
                 match uu____6093 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6188))::rest,
                         (uu____6190,None )::uu____6191) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t1 = check_no_escape (Some head1) env fvs t  in
                          let uu____6228 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____6228 with
                           | (varg,uu____6239,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1
                                  in
                               let arg =
                                 let uu____6252 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____6252)  in
                               let uu____6253 =
                                 let uu____6275 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst2,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t1))) :: outargs), (arg ::
                                   arg_rets), uu____6275, fvs)
                                  in
                               tc_args head_info uu____6253 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____6366 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___110_6373 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___110_6373.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___110_6373.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____6375 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____6375
                             then
                               let uu____6376 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6376
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ  in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1
                                in
                             let env2 =
                               let uu___111_6381 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___111_6381.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___111_6381.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___111_6381.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___111_6381.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___111_6381.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___111_6381.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___111_6381.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___111_6381.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___111_6381.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___111_6381.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___111_6381.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___111_6381.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___111_6381.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___111_6381.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___111_6381.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___111_6381.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___111_6381.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___111_6381.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___111_6381.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___111_6381.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___111_6381.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___111_6381.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___111_6381.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             (let uu____6383 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High
                                 in
                              if uu____6383
                              then
                                let uu____6384 =
                                  FStar_Syntax_Print.tag_of_term e  in
                                let uu____6385 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____6386 =
                                  FStar_Syntax_Print.term_to_string targ1  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6384 uu____6385 uu____6386
                              else ());
                             (let uu____6388 = tc_term env2 e  in
                              match uu____6388 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e1, aq)  in
                                  let uu____6404 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c
                                     in
                                  if uu____6404
                                  then
                                    let subst2 =
                                      let uu____6409 = FStar_List.hd bs  in
                                      maybe_extend_subst subst1 uu____6409 e1
                                       in
                                    tc_args head_info
                                      (subst2,
                                        ((arg, None,
                                           (FStar_Util.Inl
                                              ((c.FStar_Syntax_Syntax.eff_name),
                                                (c.FStar_Syntax_Syntax.res_typ))))
                                        :: outargs), (arg :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    (let uu____6465 =
                                       FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name
                                        in
                                     if uu____6465
                                     then
                                       let subst2 =
                                         let uu____6470 = FStar_List.hd bs
                                            in
                                         maybe_extend_subst subst1 uu____6470
                                           e1
                                          in
                                       tc_args head_info
                                         (subst2,
                                           ((arg, (Some x1),
                                              (FStar_Util.Inr c)) ::
                                           outargs), (arg :: arg_rets), g1,
                                           fvs) rest rest'
                                     else
                                       (let uu____6516 =
                                          let uu____6517 = FStar_List.hd bs
                                             in
                                          FStar_Syntax_Syntax.is_null_binder
                                            uu____6517
                                           in
                                        if uu____6516
                                        then
                                          let newx =
                                            FStar_Syntax_Syntax.new_bv
                                              (Some
                                                 (e1.FStar_Syntax_Syntax.pos))
                                              c.FStar_Syntax_Syntax.res_typ
                                             in
                                          let arg' =
                                            let uu____6526 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                newx
                                               in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____6526
                                             in
                                          tc_args head_info
                                            (subst1,
                                              ((arg, (Some newx),
                                                 (FStar_Util.Inr c)) ::
                                              outargs), (arg' :: arg_rets),
                                              g1, fvs) rest rest'
                                        else
                                          (let uu____6564 =
                                             let uu____6586 =
                                               let uu____6588 =
                                                 let uu____6589 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x1
                                                    in
                                                 FStar_Syntax_Syntax.as_arg
                                                   uu____6589
                                                  in
                                               uu____6588 :: arg_rets  in
                                             (subst1,
                                               ((arg, (Some x1),
                                                  (FStar_Util.Inr c)) ::
                                               outargs), uu____6586, g1, (x1
                                               :: fvs))
                                              in
                                           tc_args head_info uu____6564 rest
                                             rest')))))))
                      | (uu____6626,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6647) ->
                          let uu____6677 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____6677 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6700 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____6700
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____6716 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____6716 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1))
                                             in
                                          ((let uu____6730 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____6730
                                            then
                                              let uu____6731 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____6731
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____6761 when Prims.op_Negation norm1 ->
                                     let uu____6762 = unfold_whnf env tres1
                                        in
                                     aux true uu____6762
                                 | uu____6763 ->
                                     let uu____6764 =
                                       let uu____6765 =
                                         let uu____6768 =
                                           let uu____6769 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead
                                              in
                                           let uu____6770 =
                                             FStar_Util.string_of_int n_args
                                              in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6769 uu____6770
                                            in
                                         let uu____6774 =
                                           FStar_Syntax_Syntax.argpos arg  in
                                         (uu____6768, uu____6774)  in
                                       FStar_Errors.Error uu____6765  in
                                     Prims.raise uu____6764
                                  in
                               aux false chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app norm1 tf =
                 let uu____6790 =
                   let uu____6791 = FStar_Syntax_Util.unrefine tf  in
                   uu____6791.FStar_Syntax_Syntax.n  in
                 match uu____6790 with
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
                           let uu____6867 = tc_term env1 e  in
                           (match uu____6867 with
                            | (e1,c,g_e) ->
                                let uu____6880 = tc_args1 env1 tl1  in
                                (match uu____6880 with
                                 | (args2,comps,g_rest) ->
                                     let uu____6902 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____6902)))
                        in
                     let uu____6913 = tc_args1 env args  in
                     (match uu____6913 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____6935 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____6955  ->
                                      match uu____6955 with
                                      | (uu____6963,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____6935
                             in
                          let ml_or_tot t r1 =
                            let uu____6979 = FStar_Options.ml_ish ()  in
                            if uu____6979
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____6982 =
                              let uu____6985 =
                                let uu____6986 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____6986 Prims.fst  in
                              FStar_TypeChecker_Util.new_uvar env uu____6985
                               in
                            ml_or_tot uu____6982 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____6995 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____6995
                            then
                              let uu____6996 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____6997 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____6998 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____6996 uu____6997 uu____6998
                            else ());
                           (let uu____7001 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7001);
                           (let comp =
                              let uu____7003 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____7008  ->
                                   fun out  ->
                                     match uu____7008 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7003
                               in
                            let uu____7017 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r
                               in
                            let uu____7024 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____7017, comp, uu____7024))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7039 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____7039 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1))
                             in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | uu____7082 ->
                     if Prims.op_Negation norm1
                     then
                       let uu____7088 = unfold_whnf env tf  in
                       check_function_app true uu____7088
                     else
                       (let uu____7090 =
                          let uu____7091 =
                            let uu____7094 =
                              FStar_TypeChecker_Err.expected_function_typ env
                                tf
                               in
                            (uu____7094, (head1.FStar_Syntax_Syntax.pos))  in
                          FStar_Errors.Error uu____7091  in
                        Prims.raise uu____7090)
                  in
               let uu____7100 =
                 let uu____7101 = FStar_Syntax_Util.unrefine thead  in
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.WHNF] env uu____7101
                  in
               check_function_app false uu____7100)

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
                  let uu____7147 =
                    FStar_List.fold_left2
                      (fun uu____7160  ->
                         fun uu____7161  ->
                           fun uu____7162  ->
                             match (uu____7160, uu____7161, uu____7162) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7206 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____7206 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____7218 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7218 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7220 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____7220) &&
                                              (let uu____7221 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____7221))
                                          in
                                       let uu____7222 =
                                         let uu____7228 =
                                           let uu____7234 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____7234]  in
                                         FStar_List.append seen uu____7228
                                          in
                                       let uu____7239 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____7222, uu____7239, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____7147 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____7268 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____7268
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____7270 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard
                          in
                       (match uu____7270 with | (c2,g) -> (e, c2, g)))
              | uu____7282 ->
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
        let uu____7304 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____7304 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7330 = branch1  in
            (match uu____7330 with
             | (cpat,uu____7350,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7392 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0
                      in
                   match uu____7392 with
                   | (pat_bvs1,exps,p) ->
                       ((let uu____7414 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____7414
                         then
                           let uu____7415 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____7416 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7415 uu____7416
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____7419 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____7419 with
                         | (env1,uu____7432) ->
                             let env11 =
                               let uu___112_7436 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___112_7436.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___112_7436.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___112_7436.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___112_7436.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___112_7436.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___112_7436.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___112_7436.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___112_7436.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___112_7436.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___112_7436.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___112_7436.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___112_7436.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___112_7436.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___112_7436.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___112_7436.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___112_7436.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___112_7436.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___112_7436.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___112_7436.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___112_7436.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___112_7436.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___112_7436.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___112_7436.FStar_TypeChecker_Env.qname_and_index)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             let uu____7438 =
                               let uu____7443 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____7455 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High
                                             in
                                          if uu____7455
                                          then
                                            let uu____7456 =
                                              FStar_Syntax_Print.term_to_string
                                                e
                                               in
                                            let uu____7457 =
                                              FStar_Syntax_Print.term_to_string
                                                pat_t
                                               in
                                            FStar_Util.print2
                                              "Checking pattern expression %s against expected type %s\n"
                                              uu____7456 uu____7457
                                          else ());
                                         (let uu____7459 = tc_term env11 e
                                             in
                                          match uu____7459 with
                                          | (e1,lc,g) ->
                                              ((let uu____7469 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High
                                                   in
                                                if uu____7469
                                                then
                                                  let uu____7470 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env e1
                                                     in
                                                  let uu____7471 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  FStar_Util.print2
                                                    "Pre-checked pattern expression %s at type %s\n"
                                                    uu____7470 uu____7471
                                                else ());
                                               (let g' =
                                                  FStar_TypeChecker_Rel.teq
                                                    env
                                                    lc.FStar_Syntax_Syntax.res_typ
                                                    expected_pat_t
                                                   in
                                                let g1 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g'
                                                   in
                                                let uu____7475 =
                                                  let uu____7476 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___113_7477 = g1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___113_7477.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___113_7477.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___113_7477.FStar_TypeChecker_Env.implicits)
                                                       })
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____7476
                                                    FStar_TypeChecker_Rel.resolve_implicits
                                                   in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e1
                                                   in
                                                let uvars_to_string uvs =
                                                  let uu____7491 =
                                                    let uu____7493 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____7493
                                                      (FStar_List.map
                                                         (fun uu____7517  ->
                                                            match uu____7517
                                                            with
                                                            | (u,uu____7522)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u))
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____7491
                                                    (FStar_String.concat ", ")
                                                   in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e'
                                                   in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t
                                                   in
                                                (let uu____7535 =
                                                   let uu____7536 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2
                                                      in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation
                                                     uu____7536
                                                    in
                                                 if uu____7535
                                                 then
                                                   let unresolved =
                                                     let uu____7543 =
                                                       FStar_Util.set_difference
                                                         uvs1 uvs2
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____7543
                                                       FStar_Util.set_elements
                                                      in
                                                   let uu____7557 =
                                                     let uu____7558 =
                                                       let uu____7561 =
                                                         let uu____7562 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env e'
                                                            in
                                                         let uu____7563 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env
                                                             expected_pat_t
                                                            in
                                                         let uu____7564 =
                                                           let uu____7565 =
                                                             FStar_All.pipe_right
                                                               unresolved
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____7577
                                                                     ->
                                                                    match uu____7577
                                                                    with
                                                                    | 
                                                                    (u,uu____7585)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____7565
                                                             (FStar_String.concat
                                                                ", ")
                                                            in
                                                         FStar_Util.format3
                                                           "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                           uu____7562
                                                           uu____7563
                                                           uu____7564
                                                          in
                                                       (uu____7561,
                                                         (p.FStar_Syntax_Syntax.p))
                                                        in
                                                     FStar_Errors.Error
                                                       uu____7558
                                                      in
                                                   Prims.raise uu____7557
                                                 else ());
                                                (let uu____7600 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High
                                                    in
                                                 if uu____7600
                                                 then
                                                   let uu____7601 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env e1
                                                      in
                                                   FStar_Util.print1
                                                     "Done checking pattern expression %s\n"
                                                     uu____7601
                                                 else ());
                                                (e1, e'))))))
                                  in
                               FStar_All.pipe_right uu____7443
                                 FStar_List.unzip
                                in
                             (match uu____7438 with
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
                 let uu____7632 =
                   let uu____7636 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____7636
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____7632 with
                  | (scrutinee_env,uu____7649) ->
                      let uu____7652 = tc_pat true pat_t pattern  in
                      (match uu____7652 with
                       | (pattern1,pat_bvs1,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____7680 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____7695 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____7695
                                 then
                                   Prims.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____7703 =
                                      let uu____7707 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool
                                         in
                                      tc_term uu____7707 e  in
                                    match uu____7703 with
                                    | (e1,c,g) -> ((Some e1), g))
                              in
                           (match uu____7680 with
                            | (when_clause1,g_when) ->
                                let uu____7727 = tc_term pat_env branch_exp
                                   in
                                (match uu____7727 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____7746 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_30  -> Some _0_30)
                                             uu____7746
                                        in
                                     let uu____7748 =
                                       let eqs =
                                         let uu____7754 =
                                           let uu____7755 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____7755  in
                                         if uu____7754
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
                                                     | uu____7769 ->
                                                         let clause =
                                                           let uu____7771 =
                                                             env.FStar_TypeChecker_Env.universe_of
                                                               env pat_t
                                                              in
                                                           FStar_Syntax_Util.mk_eq2
                                                             uu____7771 pat_t
                                                             scrutinee_tm e1
                                                            in
                                                         (match fopt with
                                                          | None  ->
                                                              Some clause
                                                          | Some f ->
                                                              let uu____7774
                                                                =
                                                                FStar_Syntax_Util.mk_disj
                                                                  clause f
                                                                 in
                                                              FStar_All.pipe_left
                                                                (fun _0_31 
                                                                   ->
                                                                   Some _0_31)
                                                                uu____7774))
                                                None)
                                          in
                                       let uu____7784 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch
                                          in
                                       match uu____7784 with
                                       | (c1,g_branch1) ->
                                           let uu____7794 =
                                             match (eqs, when_condition) with
                                             | uu____7801 when
                                                 let uu____7806 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation uu____7806
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
                                                 let uu____7814 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____7815 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____7814, uu____7815)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____7822 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____7822
                                                    in
                                                 let uu____7823 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____7824 =
                                                   let uu____7825 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____7825 g_when
                                                    in
                                                 (uu____7823, uu____7824)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let uu____7831 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____7831, g_when)
                                              in
                                           (match uu____7794 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let uu____7839 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs1 c_weak
                                                   in
                                                let uu____7840 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    binders g_when_weak
                                                   in
                                                (uu____7839, uu____7840,
                                                  g_branch1))
                                        in
                                     (match uu____7748 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____7853 =
                                              let uu____7854 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____7854
                                               in
                                            if uu____7853
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____7885 =
                                                     let uu____7886 =
                                                       let uu____7887 =
                                                         let uu____7889 =
                                                           let uu____7893 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____7893
                                                            in
                                                         Prims.snd uu____7889
                                                          in
                                                       FStar_List.length
                                                         uu____7887
                                                        in
                                                     uu____7886 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____7885
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____7902 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____7902 with
                                                     | None  -> []
                                                     | uu____7909 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None
                                                            in
                                                         let disc1 =
                                                           let uu____7917 =
                                                             let uu____7918 =
                                                               let uu____7919
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____7919]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____7918
                                                              in
                                                           uu____7917 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____7924 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool
                                                            in
                                                         [uu____7924]
                                                   else []  in
                                                 let fail uu____7932 =
                                                   let uu____7933 =
                                                     let uu____7934 =
                                                       FStar_Range.string_of_range
                                                         pat_exp.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____7935 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp
                                                        in
                                                     let uu____7936 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____7934 uu____7935
                                                       uu____7936
                                                      in
                                                   failwith uu____7933  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____7957) ->
                                                       head_constructor t1
                                                   | uu____7963 -> fail ()
                                                    in
                                                 let pat_exp1 =
                                                   let uu____7966 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7966
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
                                                     let uu____7983 =
                                                       let uu____7984 =
                                                         tc_constant
                                                           pat_exp1.FStar_Syntax_Syntax.pos
                                                           c2
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____7984
                                                         scrutinee_tm1
                                                         pat_exp1
                                                        in
                                                     [uu____7983]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                   _
                                                   |FStar_Syntax_Syntax.Tm_fvar
                                                   _ ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp1
                                                        in
                                                     let uu____7992 =
                                                       let uu____7993 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____7993
                                                        in
                                                     if uu____7992
                                                     then []
                                                     else
                                                       (let uu____8000 =
                                                          head_constructor
                                                            pat_exp1
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8000)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____8027 =
                                                       let uu____8028 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____8028
                                                        in
                                                     if uu____8027
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8037 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8053
                                                                     ->
                                                                    match uu____8053
                                                                    with
                                                                    | 
                                                                    (ei,uu____8060)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____8070
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____8070
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8077
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8084
                                                                    =
                                                                    let uu____8085
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None  in
                                                                    let uu____8090
                                                                    =
                                                                    let uu____8091
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____8091]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8085
                                                                    uu____8090
                                                                     in
                                                                    uu____8084
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____8037
                                                            FStar_List.flatten
                                                           in
                                                        let uu____8103 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____8103
                                                          sub_term_guards)
                                                 | uu____8107 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8119 =
                                                   let uu____8120 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____8120
                                                    in
                                                 if uu____8119
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8123 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8123
                                                       in
                                                    let uu____8126 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____8126 with
                                                    | (k,uu____8130) ->
                                                        let uu____8131 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____8131
                                                         with
                                                         | (t1,uu____8136,uu____8137)
                                                             -> t1))
                                                  in
                                               let branch_guard =
                                                 let uu____8139 =
                                                   FStar_All.pipe_right
                                                     norm_disj_exps
                                                     (FStar_List.map
                                                        (build_and_check_branch_guard
                                                           scrutinee_tm))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8139
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
                                          ((let uu____8150 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____8150
                                            then
                                              let uu____8151 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8151
                                            else ());
                                           (let uu____8153 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            (uu____8153, branch_guard, c1,
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
          let uu____8171 = check_let_bound_def true env1 lb  in
          (match uu____8171 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8185 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then (g1, e1, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8196 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____8196
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____8198 =
                      let uu____8203 =
                        let uu____8209 =
                          let uu____8214 =
                            let uu____8222 = c1.FStar_Syntax_Syntax.comp ()
                               in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8222)
                             in
                          [uu____8214]  in
                        FStar_TypeChecker_Util.generalize env1 uu____8209  in
                      FStar_List.hd uu____8203  in
                    match uu____8198 with
                    | (uu____8251,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11)))
                  in
               (match uu____8185 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8262 =
                      let uu____8267 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____8267
                      then
                        let uu____8272 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____8272 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8289 =
                                   FStar_Options.warn_top_level_effects ()
                                    in
                                 if uu____8289
                                 then
                                   let uu____8290 =
                                     FStar_TypeChecker_Env.get_range env1  in
                                   FStar_Errors.warn uu____8290
                                     FStar_TypeChecker_Err.top_level_effect
                                 else ());
                                (let uu____8292 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____8292, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8310 = c11.FStar_Syntax_Syntax.comp ()
                               in
                            FStar_All.pipe_right uu____8310
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1)
                             in
                          let e21 =
                            let uu____8318 = FStar_Syntax_Util.is_pure_comp c
                               in
                            if uu____8318
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
                    (match uu____8262 with
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
                           let uu____8350 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos
                              in
                           (uu____8350,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8369 -> failwith "Impossible"

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
            let uu___114_8390 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___114_8390.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___114_8390.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___114_8390.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___114_8390.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___114_8390.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___114_8390.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___114_8390.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___114_8390.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___114_8390.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___114_8390.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___114_8390.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___114_8390.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___114_8390.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___114_8390.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___114_8390.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___114_8390.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___114_8390.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___114_8390.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___114_8390.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___114_8390.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___114_8390.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___114_8390.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___114_8390.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____8391 =
            let uu____8397 =
              let uu____8398 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____8398 Prims.fst  in
            check_let_bound_def false uu____8397 lb  in
          (match uu____8391 with
           | (e1,uu____8410,c1,g1,annotated) ->
               let x =
                 let uu___115_8415 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___115_8415.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___115_8415.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 }  in
               let uu____8416 =
                 let uu____8419 =
                   let uu____8420 = FStar_Syntax_Syntax.mk_binder x  in
                   [uu____8420]  in
                 FStar_Syntax_Subst.open_term uu____8419 e2  in
               (match uu____8416 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb  in
                    let x1 = Prims.fst xbinder  in
                    let uu____8432 =
                      let uu____8436 = FStar_TypeChecker_Env.push_bv env2 x1
                         in
                      tc_term uu____8436 e21  in
                    (match uu____8432 with
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
                           let uu____8451 =
                             let uu____8454 =
                               let uu____8455 =
                                 let uu____8463 =
                                   FStar_Syntax_Subst.close xb e23  in
                                 ((false, [lb1]), uu____8463)  in
                               FStar_Syntax_Syntax.Tm_let uu____8455  in
                             FStar_Syntax_Syntax.mk uu____8454  in
                           uu____8451
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
                           let uu____8478 =
                             let uu____8479 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ
                                in
                             let uu____8480 =
                               FStar_Syntax_Syntax.bv_to_name x1  in
                             FStar_Syntax_Util.mk_eq2 uu____8479
                               c1.FStar_Syntax_Syntax.res_typ uu____8480 e11
                              in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8478
                            in
                         let g21 =
                           let uu____8482 =
                             let uu____8483 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard uu____8483 g2
                              in
                           FStar_TypeChecker_Rel.close_guard xb uu____8482
                            in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                            in
                         let uu____8485 =
                           let uu____8486 =
                             FStar_TypeChecker_Env.expected_typ env2  in
                           FStar_Option.isSome uu____8486  in
                         if uu____8485
                         then
                           let tt =
                             let uu____8492 =
                               FStar_TypeChecker_Env.expected_typ env2  in
                             FStar_All.pipe_right uu____8492 FStar_Option.get
                              in
                           ((let uu____8496 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____8496
                             then
                               let uu____8497 =
                                 FStar_Syntax_Print.term_to_string tt  in
                               let uu____8498 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____8497 uu____8498
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ
                               in
                            (let uu____8503 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____8503
                             then
                               let uu____8504 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               let uu____8505 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8504 uu____8505
                             else ());
                            (e4,
                              ((let uu___116_8507 = cres  in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___116_8507.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___116_8507.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___116_8507.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8508 -> failwith "Impossible"

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
          let uu____8529 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____8529 with
           | (lbs1,e21) ->
               let uu____8540 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8540 with
                | (env0,topt) ->
                    let uu____8551 = build_let_rec_env true env0 lbs1  in
                    (match uu____8551 with
                     | (lbs2,rec_env) ->
                         let uu____8562 = check_let_recs rec_env lbs2  in
                         (match uu____8562 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8574 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____8574
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____8578 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____8578
                                  (fun _0_33  -> Some _0_33)
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
                                     let uu____8602 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____8624 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____8624)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8602
                                      in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____8644  ->
                                           match uu____8644 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e)))
                                 in
                              let cres =
                                let uu____8669 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____8669
                                 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____8678 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21
                                   in
                                match uu____8678 with
                                | (lbs5,e22) ->
                                    let uu____8689 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____8704 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env1 g_lbs1
                                       in
                                    (uu____8689, cres, uu____8704)))))))
      | uu____8707 -> failwith "Impossible"

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
          let uu____8728 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____8728 with
           | (lbs1,e21) ->
               let uu____8739 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8739 with
                | (env0,topt) ->
                    let uu____8750 = build_let_rec_env false env0 lbs1  in
                    (match uu____8750 with
                     | (lbs2,rec_env) ->
                         let uu____8761 = check_let_recs rec_env lbs2  in
                         (match uu____8761 with
                          | (lbs3,g_lbs) ->
                              let uu____8772 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___117_8783 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___117_8783.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___117_8783.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___118_8785 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___118_8785.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___118_8785.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___118_8785.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___118_8785.FStar_Syntax_Syntax.lbdef)
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
                              (match uu____8772 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____8802 = tc_term env2 e21  in
                                   (match uu____8802 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____8813 =
                                            let uu____8814 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              uu____8814 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____8813
                                           in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_comp
                                            env2 bvs cres
                                           in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ
                                           in
                                        let cres2 =
                                          let uu___119_8818 = cres1  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___119_8818.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___119_8818.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___119_8818.FStar_Syntax_Syntax.comp)
                                          }  in
                                        let uu____8819 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____8819 with
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
                                              | Some uu____8848 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres
                                                     in
                                                  let cres3 =
                                                    let uu___120_8853 = cres2
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___120_8853.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___120_8853.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___120_8853.FStar_Syntax_Syntax.comp)
                                                    }  in
                                                  (e, cres3, guard)))))))))
      | uu____8856 -> failwith "Impossible"

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
          let uu____8872 = FStar_Syntax_Util.arrow_formals_comp t  in
          match uu____8872 with
          | (uu____8878,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c)
                 in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)
           in
        let uu____8889 =
          FStar_List.fold_left
            (fun uu____8896  ->
               fun lb  ->
                 match uu____8896 with
                 | (lbs1,env1) ->
                     let uu____8908 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____8908 with
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
                              (let uu____8922 =
                                 let uu____8926 =
                                   let uu____8927 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left Prims.fst uu____8927
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___121_8932 = env0  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___121_8932.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___121_8932.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___121_8932.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___121_8932.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___121_8932.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___121_8932.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___121_8932.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___121_8932.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___121_8932.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___121_8932.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___121_8932.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___121_8932.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___121_8932.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___121_8932.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___121_8932.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___121_8932.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___121_8932.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___121_8932.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___121_8932.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___121_8932.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___121_8932.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___121_8932.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___121_8932.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____8926
                                  in
                               match uu____8922 with
                               | (t1,uu____8934,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let uu____8938 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left Prims.ignore
                                       uu____8938);
                                    norm env0 t1))
                             in
                          let env3 =
                            let uu____8940 =
                              (termination_check_enabled t1) &&
                                (FStar_TypeChecker_Env.should_verify env2)
                               in
                            if uu____8940
                            then
                              let uu___122_8941 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___122_8941.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___122_8941.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___122_8941.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___122_8941.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___122_8941.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___122_8941.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___122_8941.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___122_8941.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___122_8941.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___122_8941.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___122_8941.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___122_8941.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___122_8941.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___122_8941.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___122_8941.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___122_8941.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___122_8941.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___122_8941.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___122_8941.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___122_8941.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___122_8941.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___122_8941.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___122_8941.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1)
                             in
                          let lb1 =
                            let uu___123_8951 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___123_8951.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___123_8951.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____8889 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____8965 =
        let uu____8970 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____8981 =
                    let uu____8985 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    tc_tot_or_gtot_term uu____8985
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____8981 with
                  | (e,c,g) ->
                      ((let uu____8992 =
                          let uu____8993 = FStar_Syntax_Util.is_total_lcomp c
                             in
                          Prims.op_Negation uu____8993  in
                        if uu____8992
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
        FStar_All.pipe_right uu____8970 FStar_List.unzip  in
      match uu____8965 with
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
        let uu____9022 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____9022 with
        | (env1,uu____9032) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____9038 = check_lbtyp top_level env lb  in
            (match uu____9038 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____9064 =
                     tc_maybe_toplevel_term
                       (let uu___124_9068 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___124_9068.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___124_9068.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___124_9068.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___124_9068.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___124_9068.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___124_9068.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___124_9068.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___124_9068.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___124_9068.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___124_9068.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___124_9068.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___124_9068.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___124_9068.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___124_9068.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___124_9068.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___124_9068.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___124_9068.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___124_9068.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___124_9068.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___124_9068.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___124_9068.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___124_9068.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___124_9068.FStar_TypeChecker_Env.qname_and_index)
                        }) e11
                      in
                   match uu____9064 with
                   | (e12,c1,g1) ->
                       let uu____9077 =
                         let uu____9080 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9083  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9080 e12 c1 wf_annot
                          in
                       (match uu____9077 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____9093 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____9093
                              then
                                let uu____9094 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____9095 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____9096 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9094 uu____9095 uu____9096
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
        | uu____9122 ->
            let uu____9123 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____9123 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9150 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9150)
                 else
                   (let uu____9155 = FStar_Syntax_Util.type_u ()  in
                    match uu____9155 with
                    | (k,uu____9166) ->
                        let uu____9167 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____9167 with
                         | (t2,uu____9179,g) ->
                             ((let uu____9182 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____9182
                               then
                                 let uu____9183 =
                                   let uu____9184 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____9184  in
                                 let uu____9185 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9183 uu____9185
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____9188 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9188))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) *
        FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t *
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9193  ->
      match uu____9193 with
      | (x,imp) ->
          let uu____9204 = FStar_Syntax_Util.type_u ()  in
          (match uu____9204 with
           | (tu,u) ->
               ((let uu____9216 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____9216
                 then
                   let uu____9217 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____9218 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____9219 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9217 uu____9218 uu____9219
                 else ());
                (let uu____9221 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____9221 with
                 | (t,uu____9232,g) ->
                     let x1 =
                       ((let uu___125_9237 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___125_9237.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___125_9237.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____9239 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____9239
                       then
                         let uu____9240 =
                           FStar_Syntax_Print.bv_to_string (Prims.fst x1)  in
                         let uu____9241 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9240 uu____9241
                       else ());
                      (let uu____9243 = push_binding env x1  in
                       (x1, uu____9243, g, u))))))

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
            let uu____9294 = tc_binder env1 b  in
            (match uu____9294 with
             | (b1,env',g,u) ->
                 let uu____9317 = aux env' bs2  in
                 (match uu____9317 with
                  | (bs3,env'1,g',us) ->
                      let uu____9346 =
                        let uu____9347 =
                          FStar_TypeChecker_Rel.close_guard [b1] g'  in
                        FStar_TypeChecker_Rel.conj_guard g uu____9347  in
                      ((b1 :: bs3), env'1, uu____9346, (u :: us))))
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
          (fun uu____9390  ->
             fun uu____9391  ->
               match (uu____9390, uu____9391) with
               | ((t,imp),(args1,g)) ->
                   let uu____9428 = tc_term env1 t  in
                   (match uu____9428 with
                    | (t1,uu____9438,g') ->
                        let uu____9440 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____9440))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9458  ->
             match uu____9458 with
             | (pats1,g) ->
                 let uu____9472 = tc_args env p  in
                 (match uu____9472 with
                  | (args,g') ->
                      let uu____9480 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____9480))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____9488 = tc_maybe_toplevel_term env e  in
      match uu____9488 with
      | (e1,c,g) ->
          let uu____9498 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____9498
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = c.FStar_Syntax_Syntax.comp ()  in
             let c2 = norm_c env c1  in
             let uu____9508 =
               let uu____9511 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____9511
               then
                 let uu____9514 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____9514, false)
               else
                 (let uu____9516 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____9516, true))
                in
             match uu____9508 with
             | (target_comp,allow_ghost) ->
                 let uu____9522 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____9522 with
                  | Some g' ->
                      let uu____9528 = FStar_TypeChecker_Rel.conj_guard g1 g'
                         in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____9528)
                  | uu____9529 ->
                      if allow_ghost
                      then
                        let uu____9534 =
                          let uu____9535 =
                            let uu____9538 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2
                               in
                            (uu____9538, (e1.FStar_Syntax_Syntax.pos))  in
                          FStar_Errors.Error uu____9535  in
                        Prims.raise uu____9534
                      else
                        (let uu____9543 =
                           let uu____9544 =
                             let uu____9547 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2
                                in
                             (uu____9547, (e1.FStar_Syntax_Syntax.pos))  in
                           FStar_Errors.Error uu____9544  in
                         Prims.raise uu____9543)))

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
      let uu____9560 = tc_tot_or_gtot_term env t  in
      match uu____9560 with
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
      (let uu____9580 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9580
       then
         let uu____9581 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____9581
       else ());
      (let env1 =
         let uu___126_9584 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___126_9584.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___126_9584.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___126_9584.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___126_9584.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___126_9584.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___126_9584.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___126_9584.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___126_9584.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___126_9584.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___126_9584.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___126_9584.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___126_9584.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___126_9584.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___126_9584.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___126_9584.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___126_9584.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___126_9584.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___126_9584.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___126_9584.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___126_9584.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___126_9584.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____9587 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____9603) ->
             let uu____9604 =
               let uu____9605 =
                 let uu____9608 = FStar_TypeChecker_Env.get_range env1  in
                 ((Prims.strcat "Implicit argument: " msg), uu____9608)  in
               FStar_Errors.Error uu____9605  in
             Prims.raise uu____9604
          in
       match uu____9587 with
       | (t,c,g) ->
           let uu____9618 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____9618
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____9625 =
                let uu____9626 =
                  let uu____9629 =
                    let uu____9630 = FStar_Syntax_Print.term_to_string e  in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____9630
                     in
                  let uu____9631 = FStar_TypeChecker_Env.get_range env1  in
                  (uu____9629, uu____9631)  in
                FStar_Errors.Error uu____9626  in
              Prims.raise uu____9625))
  
let level_of_type_fail env e t =
  let uu____9652 =
    let uu____9653 =
      let uu____9656 =
        let uu____9657 = FStar_Syntax_Print.term_to_string e  in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____9657 t
         in
      let uu____9658 = FStar_TypeChecker_Env.get_range env  in
      (uu____9656, uu____9658)  in
    FStar_Errors.Error uu____9653  in
  Prims.raise uu____9652 
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____9675 =
            let uu____9676 = FStar_Syntax_Util.unrefine t1  in
            uu____9676.FStar_Syntax_Syntax.n  in
          match uu____9675 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____9680 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____9683 = FStar_Syntax_Util.type_u ()  in
                 match uu____9683 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___129_9689 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___129_9689.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___129_9689.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___129_9689.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___129_9689.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___129_9689.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___129_9689.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___129_9689.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___129_9689.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___129_9689.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___129_9689.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___129_9689.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___129_9689.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___129_9689.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___129_9689.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___129_9689.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___129_9689.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___129_9689.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___129_9689.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___129_9689.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___129_9689.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___129_9689.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___129_9689.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___129_9689.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____9693 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____9693
                       | uu____9694 ->
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
      let uu____9703 =
        let uu____9704 = FStar_Syntax_Subst.compress e  in
        uu____9704.FStar_Syntax_Syntax.n  in
      match uu____9703 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____9713 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____9724) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____9749,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____9764) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9771 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9771 with | (uu____9780,t) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____9782,FStar_Util.Inl t,uu____9784) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____9803,FStar_Util.Inr c,uu____9805) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____9835;
             FStar_Syntax_Syntax.pos = uu____9836;
             FStar_Syntax_Syntax.vars = uu____9837;_},us)
          ->
          let uu____9843 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9843 with
           | (us',t) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____9859 =
                     let uu____9860 =
                       let uu____9863 = FStar_TypeChecker_Env.get_range env
                          in
                       ("Unexpected number of universe instantiations",
                         uu____9863)
                        in
                     FStar_Errors.Error uu____9860  in
                   Prims.raise uu____9859)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____9871 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____9872 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____9880) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____9897 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9897 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____9908  ->
                      match uu____9908 with
                      | (b,uu____9912) ->
                          let uu____9913 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____9913) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____9918 = universe_of_aux env res  in
                 level_of_type env res uu____9918  in
               let u_c =
                 let uu____9920 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____9920 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____9923 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____9923
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
                let uu____10009 = universe_of_aux env hd3  in
                (uu____10009, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10019,hd4::uu____10021) ->
                let uu____10068 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____10068 with
                 | (uu____10078,uu____10079,hd5) ->
                     let uu____10095 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____10095 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10130 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____10132 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____10132 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10167 ->
                let uu____10168 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____10168 with
                 | (env1,uu____10182) ->
                     let env2 =
                       let uu___130_10186 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___130_10186.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___130_10186.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___130_10186.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___130_10186.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___130_10186.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___130_10186.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___130_10186.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___130_10186.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___130_10186.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___130_10186.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___130_10186.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___130_10186.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___130_10186.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___130_10186.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___130_10186.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___130_10186.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___130_10186.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___130_10186.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___130_10186.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___130_10186.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___130_10186.FStar_TypeChecker_Env.qname_and_index)
                       }  in
                     ((let uu____10188 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____10188
                       then
                         let uu____10189 =
                           let uu____10190 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____10190  in
                         let uu____10191 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10189 uu____10191
                       else ());
                      (let uu____10193 = tc_term env2 hd3  in
                       match uu____10193 with
                       | (uu____10206,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10207;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10209;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10210;_},g)
                           ->
                           ((let uu____10220 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____10220 Prims.ignore);
                            (t, args1)))))
             in
          let uu____10228 = type_of_head true hd1 args  in
          (match uu____10228 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____10257 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____10257 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____10290 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____10290)))
      | FStar_Syntax_Syntax.Tm_match (uu____10293,hd1::uu____10295) ->
          let uu____10342 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____10342 with
           | (uu____10345,uu____10346,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____10362,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____10396 = universe_of_aux env e  in
      level_of_type env e uu____10396
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____10409 = tc_binders env tps  in
      match uu____10409 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
  