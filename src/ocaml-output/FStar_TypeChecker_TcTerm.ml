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
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
           let uu____43 =
             let uu____44 =
               let uu____45 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____46 =
                 let uu____49 = FStar_Syntax_Syntax.as_arg tl1  in [uu____49]
                  in
               uu____45 :: uu____46  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____44
              in
           uu____43 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___84_57  ->
    match uu___84_57 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____60 -> false
  
let steps :
  'Auu____67 . 'Auu____67 -> FStar_TypeChecker_Normalize.step Prims.list =
  fun env  ->
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
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
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
            | uu____121 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____129 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____129 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____139 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____141 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____141
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____143 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____144 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____143 uu____144
                             in
                          let uu____145 =
                            let uu____146 =
                              let uu____151 =
                                FStar_TypeChecker_Env.get_range env  in
                              (msg, uu____151)  in
                            FStar_Errors.Error uu____146  in
                          FStar_Exn.raise uu____145  in
                        let s =
                          let uu____153 =
                            let uu____154 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____154
                             in
                          FStar_TypeChecker_Util.new_uvar env uu____153  in
                        let uu____163 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s  in
                        match uu____163 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____168 -> fail ()))
             in
          aux false kt
  
let push_binding :
  'Auu____177 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____177) FStar_Pervasives_Native.tuple2 ->
        FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
  
let maybe_extend_subst :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____210 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____210
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
  
let set_lcomp_result :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___91_226 = lc  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___91_226.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___91_226.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____229  ->
             let uu____230 = lc.FStar_Syntax_Syntax.comp ()  in
             FStar_Syntax_Util.set_result_typ uu____230 t)
      }
  
let memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> e 
let value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          let should_return t =
            let uu____281 =
              let uu____282 = FStar_Syntax_Subst.compress t  in
              uu____282.FStar_Syntax_Syntax.n  in
            match uu____281 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____285,c) ->
                let uu____303 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                if uu____303
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c)
                     in
                  let uu____305 =
                    let uu____306 = FStar_Syntax_Subst.compress t1  in
                    uu____306.FStar_Syntax_Syntax.n  in
                  (match uu____305 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____310 -> false
                   | uu____311 -> true)
                else false
            | uu____313 -> true  in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____316 =
                  let uu____319 =
                    (let uu____322 = should_return t  in
                     Prims.op_Negation uu____322) ||
                      (let uu____324 =
                         FStar_TypeChecker_Env.should_verify env  in
                       Prims.op_Negation uu____324)
                     in
                  if uu____319
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e  in
                FStar_Syntax_Util.lcomp_of_comp uu____316
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____332 =
            let uu____339 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____339 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____350 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High  in
                  if uu____350
                  then
                    let uu____351 = FStar_Syntax_Print.term_to_string t  in
                    let uu____352 = FStar_Syntax_Print.term_to_string t'  in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____351
                      uu____352
                  else ());
                 (let uu____354 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t'
                     in
                  match uu____354 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                      let uu____370 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____370 with
                       | (e2,g) ->
                           ((let uu____384 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____384
                             then
                               let uu____385 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____386 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____387 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____388 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____385 uu____386 uu____387 uu____388
                             else ());
                            (let msg =
                               let uu____395 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               if uu____395
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_39  ->
                                      FStar_Pervasives_Native.Some _0_39)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             let uu____412 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1
                                in
                             match uu____412 with
                             | (lc2,g2) ->
                                 ((memo_tk e2 t'), (set_lcomp_result lc2 t'),
                                   g2))))))
             in
          match uu____332 with
          | (e1,lc1,g) ->
              ((let uu____435 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                if uu____435
                then
                  let uu____436 = FStar_Syntax_Print.lcomp_to_string lc1  in
                  FStar_Util.print1 "Return comp type is %s\n" uu____436
                else ());
               (e1, lc1, g))
  
let comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____462 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____462 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____472 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____472 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
  
let check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun copt  ->
      fun uu____508  ->
        match uu____508 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____537 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____537
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____539 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____539
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____541 =
              match copt with
              | FStar_Pervasives_Native.Some uu____554 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____557 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____559 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____559))
                     in
                  if uu____557
                  then
                    let uu____566 =
                      let uu____569 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____569  in
                    (uu____566, c)
                  else
                    (let uu____573 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____573
                     then
                       let uu____580 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____580)
                     else
                       (let uu____584 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____584
                        then
                          let uu____591 =
                            let uu____594 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____594  in
                          (uu____591, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____541 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____620 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c
                         in
                      (match uu____620 with
                       | (e1,uu____634,g) ->
                           let g1 =
                             let uu____637 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_TypeChecker_Util.label_guard uu____637
                               "could not prove post-condition" g
                              in
                           ((let uu____639 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low
                                in
                             if uu____639
                             then
                               let uu____640 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____641 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1
                                  in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____640 uu____641
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2)
                                in
                             (e2, expected_c, g1))))))
  
let no_logical_guard :
  'Auu____652 'Auu____653 .
    FStar_TypeChecker_Env.env ->
      ('Auu____653,'Auu____652,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____653,'Auu____652,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____673  ->
      match uu____673 with
      | (te,kt,f) ->
          let uu____683 = FStar_TypeChecker_Rel.guard_form f  in
          (match uu____683 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____691 =
                 let uu____692 =
                   let uu____697 =
                     FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                       env f1
                      in
                   let uu____698 = FStar_TypeChecker_Env.get_range env  in
                   (uu____697, uu____698)  in
                 FStar_Errors.Error uu____692  in
               FStar_Exn.raise uu____691)
  
let print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____709 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____709 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None"
    | FStar_Pervasives_Native.Some t ->
        let uu____713 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____713
  
let check_smt_pat :
  'Auu____724 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____724) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____757 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____757
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____758;
                  FStar_Syntax_Syntax.effect_name = uu____759;
                  FStar_Syntax_Syntax.result_typ = uu____760;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____764)::[];
                  FStar_Syntax_Syntax.flags = uu____765;_}
                ->
                let pat_vars =
                  let uu____813 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats
                     in
                  FStar_Syntax_Free.names uu____813  in
                let uu____814 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____841  ->
                          match uu____841 with
                          | (b,uu____847) ->
                              let uu____848 = FStar_Util.set_mem b pat_vars
                                 in
                              Prims.op_Negation uu____848))
                   in
                (match uu____814 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____854) ->
                     let uu____859 =
                       let uu____860 = FStar_Syntax_Print.bv_to_string x  in
                       FStar_Util.format1
                         "Pattern misses at least one bound variable: %s"
                         uu____860
                        in
                     FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____859)
            | uu____861 -> failwith "Impossible"
          else ()
  
let guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____891 =
          let uu____892 = FStar_TypeChecker_Env.should_verify env  in
          Prims.op_Negation uu____892  in
        if uu____891
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env  in
               let env1 =
                 let uu___92_923 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___92_923.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___92_923.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___92_923.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___92_923.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___92_923.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___92_923.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___92_923.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___92_923.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___92_923.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___92_923.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___92_923.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___92_923.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___92_923.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___92_923.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___92_923.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___92_923.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___92_923.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___92_923.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___92_923.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___92_923.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___92_923.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___92_923.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___92_923.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___92_923.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___92_923.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___92_923.FStar_TypeChecker_Env.is_native_tactic)
                 }  in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Parser_Const.precedes_lid
                  in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____957  ->
                           match uu____957 with
                           | (b,uu____965) ->
                               let t =
                                 let uu____967 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort
                                    in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____967
                                  in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____970 -> []
                                | FStar_Syntax_Syntax.Tm_arrow uu____971 ->
                                    []
                                | uu____984 ->
                                    let uu____985 =
                                      FStar_Syntax_Syntax.bv_to_name b  in
                                    [uu____985])))
                    in
                 let as_lex_list dec =
                   let uu____990 = FStar_Syntax_Util.head_and_args dec  in
                   match uu____990 with
                   | (head1,uu____1006) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.lexcons_lid
                            -> dec
                        | uu____1028 -> mk_lex_list [dec])
                    in
                 let cflags = FStar_Syntax_Util.comp_flags c  in
                 let uu____1032 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___85_1041  ->
                           match uu___85_1041 with
                           | FStar_Syntax_Syntax.DECREASES uu____1042 -> true
                           | uu____1045 -> false))
                    in
                 match uu____1032 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.DECREASES dec) -> as_lex_list dec
                 | uu____1049 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions  in
                     (match xs with
                      | x::[] -> x
                      | uu____1058 -> mk_lex_list xs)
                  in
               let previous_dec = decreases_clause actuals expected_c  in
               let guard_one_letrec uu____1075 =
                 match uu____1075 with
                 | (l,t) ->
                     let uu____1088 =
                       let uu____1089 = FStar_Syntax_Subst.compress t  in
                       uu____1089.FStar_Syntax_Syntax.n  in
                     (match uu____1088 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____1148  ->
                                    match uu____1148 with
                                    | (x,imp) ->
                                        let uu____1159 =
                                          FStar_Syntax_Syntax.is_null_bv x
                                           in
                                        if uu____1159
                                        then
                                          let uu____1164 =
                                            let uu____1165 =
                                              let uu____1168 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____1168
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____1165
                                              x.FStar_Syntax_Syntax.sort
                                             in
                                          (uu____1164, imp)
                                        else (x, imp)))
                             in
                          let uu____1170 =
                            FStar_Syntax_Subst.open_comp formals1 c  in
                          (match uu____1170 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1  in
                               let precedes1 =
                                 let uu____1187 =
                                   let uu____1188 =
                                     let uu____1189 =
                                       FStar_Syntax_Syntax.as_arg dec  in
                                     let uu____1190 =
                                       let uu____1193 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec
                                          in
                                       [uu____1193]  in
                                     uu____1189 :: uu____1190  in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____1188
                                    in
                                 uu____1187 FStar_Pervasives_Native.None r
                                  in
                               let uu____1196 = FStar_Util.prefix formals2
                                  in
                               (match uu____1196 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___93_1241 = last1  in
                                      let uu____1242 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___93_1241.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___93_1241.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____1242
                                      }  in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)]  in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1
                                       in
                                    ((let uu____1268 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low
                                         in
                                      if uu____1268
                                      then
                                        let uu____1269 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l
                                           in
                                        let uu____1270 =
                                          FStar_Syntax_Print.term_to_string t
                                           in
                                        let uu____1271 =
                                          FStar_Syntax_Print.term_to_string
                                            t'
                                           in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____1269 uu____1270 uu____1271
                                      else ());
                                     (l, t'))))
                      | uu____1275 ->
                          FStar_Exn.raise
                            (FStar_Errors.Error
                               ("Annotated type of 'let rec' must be an arrow",
                                 (t.FStar_Syntax_Syntax.pos))))
                  in
               FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))
  
let rec tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___94_1686 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___94_1686.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___94_1686.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___94_1686.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___94_1686.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___94_1686.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___94_1686.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___94_1686.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___94_1686.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___94_1686.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___94_1686.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___94_1686.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___94_1686.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___94_1686.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___94_1686.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___94_1686.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___94_1686.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___94_1686.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___94_1686.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___94_1686.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___94_1686.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___94_1686.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___94_1686.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___94_1686.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___94_1686.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___94_1686.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___94_1686.FStar_TypeChecker_Env.is_native_tactic)
         }) e

and tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      (let uu____1698 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____1698
       then
         let uu____1699 =
           let uu____1700 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1700  in
         let uu____1701 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____1699 uu____1701
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1710 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1741 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1748 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1765 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1766 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1767 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1768 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1769 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1786 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1799 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1806 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1812 = tc_tot_or_gtot_term env1 e1  in
           (match uu____1812 with
            | (e2,c,g) ->
                let g1 =
                  let uu___95_1829 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___95_1829.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___95_1829.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___95_1829.FStar_TypeChecker_Env.implicits)
                  }  in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1846 = FStar_Syntax_Util.type_u ()  in
           (match uu____1846 with
            | (t,u) ->
                let uu____1859 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____1859 with
                 | (e2,c,g) ->
                     let uu____1875 =
                       let uu____1890 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____1890 with
                       | (env2,uu____1912) -> tc_pats env2 pats  in
                     (match uu____1875 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___96_1946 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___96_1946.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___96_1946.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___96_1946.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____1947 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____1950 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____1947, c, uu____1950))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1958 =
             let uu____1959 = FStar_Syntax_Subst.compress e1  in
             uu____1959.FStar_Syntax_Syntax.n  in
           (match uu____1958 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1968,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1970;
                               FStar_Syntax_Syntax.lbtyp = uu____1971;
                               FStar_Syntax_Syntax.lbeff = uu____1972;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1997 =
                  let uu____2004 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____2004 e11  in
                (match uu____1997 with
                 | (e12,c1,g1) ->
                     let uu____2014 = tc_term env1 e2  in
                     (match uu____2014 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1
                              (FStar_Pervasives_Native.None, c2)
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
                            let uu____2038 =
                              let uu____2041 =
                                let uu____2042 =
                                  let uu____2055 =
                                    let uu____2062 =
                                      let uu____2065 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13)
                                         in
                                      [uu____2065]  in
                                    (false, uu____2062)  in
                                  (uu____2055, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____2042  in
                              FStar_Syntax_Syntax.mk uu____2041  in
                            uu____2038 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____2087 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e5, c, uu____2087)))
            | uu____2090 ->
                let uu____2091 = tc_term env1 e1  in
                (match uu____2091 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2113) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2130 = tc_term env1 e1  in
           (match uu____2130 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2154) ->
           let uu____2201 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____2201 with
            | (env0,uu____2215) ->
                let uu____2220 = tc_comp env0 expected_c  in
                (match uu____2220 with
                 | (expected_c1,uu____2234,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1
                        in
                     let uu____2239 =
                       let uu____2246 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____2246 e1  in
                     (match uu____2239 with
                      | (e2,c',g') ->
                          let uu____2256 =
                            let uu____2263 =
                              let uu____2268 = c'.FStar_Syntax_Syntax.comp ()
                                 in
                              (e2, uu____2268)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2263
                             in
                          (match uu____2256 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inl t_res),
                                          FStar_Pervasives_Native.None),
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Util.comp_effect_name
                                              expected_c2))))
                                   FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2
                                  in
                               let f =
                                 let uu____2323 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2323
                                  in
                               let topt1 = tc_tactic_opt env0 topt  in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2332 =
                                            FStar_Syntax_Util.mk_squash f1
                                             in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2332)
                                  in
                               let uu____2333 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____2333 with
                                | (e5,c,f2) ->
                                    let uu____2349 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2
                                       in
                                    (e5, c, uu____2349))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2353) ->
           let uu____2400 = FStar_Syntax_Util.type_u ()  in
           (match uu____2400 with
            | (k,u) ->
                let uu____2413 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____2413 with
                 | (t1,uu____2427,f) ->
                     let uu____2429 =
                       let uu____2436 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____2436 e1  in
                     (match uu____2429 with
                      | (e2,c,g) ->
                          let uu____2446 =
                            let uu____2451 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2455  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2451 e2 c f
                             in
                          (match uu____2446 with
                           | (c1,f1) ->
                               let uu____2464 =
                                 let uu____2471 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env1 uu____2471 c1
                                  in
                               (match uu____2464 with
                                | (e3,c2,f2) ->
                                    let uu____2511 =
                                      let uu____2512 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2512
                                       in
                                    (e3, c2, uu____2511))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2513;
              FStar_Syntax_Syntax.vars = uu____2514;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____2577 = FStar_Syntax_Util.head_and_args top  in
           (match uu____2577 with
            | (unary_op,uu____2599) ->
                let head1 =
                  let uu____2623 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2623
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2661);
              FStar_Syntax_Syntax.pos = uu____2662;
              FStar_Syntax_Syntax.vars = uu____2663;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____2726 = FStar_Syntax_Util.head_and_args top  in
           (match uu____2726 with
            | (unary_op,uu____2748) ->
                let head1 =
                  let uu____2772 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2772
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2810;
              FStar_Syntax_Syntax.vars = uu____2811;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2844 =
               let uu____2851 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               match uu____2851 with | (env0,uu____2865) -> tc_term env0 e1
                in
             match uu____2844 with
             | (e2,c,g) ->
                 let uu____2879 = FStar_Syntax_Util.head_and_args top  in
                 (match uu____2879 with
                  | (reify_op,uu____2901) ->
                      let u_c =
                        let uu____2923 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ  in
                        match uu____2923 with
                        | (uu____2930,c',uu____2932) ->
                            let uu____2933 =
                              let uu____2934 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ
                                 in
                              uu____2934.FStar_Syntax_Syntax.n  in
                            (match uu____2933 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2938 ->
                                 let uu____2939 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____2939 with
                                  | (t,u) ->
                                      let g_opt =
                                        FStar_TypeChecker_Rel.try_teq true
                                          env1 c'.FStar_Syntax_Syntax.res_typ
                                          t
                                         in
                                      ((match g_opt with
                                        | FStar_Pervasives_Native.Some g' ->
                                            FStar_TypeChecker_Rel.force_trivial_guard
                                              env1 g'
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____2951 =
                                              let uu____2952 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c'
                                                 in
                                              let uu____2953 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ
                                                 in
                                              let uu____2954 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ
                                                 in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2952 uu____2953
                                                uu____2954
                                               in
                                            failwith uu____2951);
                                       u)))
                         in
                      let repr =
                        let uu____2956 = c.FStar_Syntax_Syntax.comp ()  in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2956 u_c
                         in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          FStar_Pervasives_Native.None
                          top.FStar_Syntax_Syntax.pos
                         in
                      let c1 =
                        let uu____2977 = FStar_Syntax_Syntax.mk_Total repr
                           in
                        FStar_All.pipe_right uu____2977
                          FStar_Syntax_Util.lcomp_of_comp
                         in
                      let uu____2978 = comp_check_expected_typ env1 e3 c1  in
                      (match uu____2978 with
                       | (e4,c2,g') ->
                           let uu____2994 =
                             FStar_TypeChecker_Rel.conj_guard g g'  in
                           (e4, c2, uu____2994)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____2996;
              FStar_Syntax_Syntax.vars = uu____2997;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____3039 =
               let uu____3040 =
                 let uu____3041 =
                   let uu____3046 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str
                      in
                   (uu____3046, (e1.FStar_Syntax_Syntax.pos))  in
                 FStar_Errors.Error uu____3041  in
               FStar_Exn.raise uu____3040  in
             let uu____3053 = FStar_Syntax_Util.head_and_args top  in
             match uu____3053 with
             | (reflect_op,uu____3075) ->
                 let uu____3096 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____3096 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3129 =
                        let uu____3130 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____3130  in
                      if uu____3129
                      then no_reflect ()
                      else
                        (let uu____3140 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____3140 with
                         | (env_no_ex,topt) ->
                             let uu____3159 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____3179 =
                                   let uu____3182 =
                                     let uu____3183 =
                                       let uu____3198 =
                                         let uu____3201 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____3202 =
                                           let uu____3205 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____3205]  in
                                         uu____3201 :: uu____3202  in
                                       (repr, uu____3198)  in
                                     FStar_Syntax_Syntax.Tm_app uu____3183
                                      in
                                   FStar_Syntax_Syntax.mk uu____3182  in
                                 uu____3179 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____3211 =
                                 let uu____3218 =
                                   let uu____3219 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____3219
                                     FStar_Pervasives_Native.fst
                                    in
                                 tc_tot_or_gtot_term uu____3218 t  in
                               match uu____3211 with
                               | (t1,uu____3247,g) ->
                                   let uu____3249 =
                                     let uu____3250 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____3250.FStar_Syntax_Syntax.n  in
                                   (match uu____3249 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____3265,(res,uu____3267)::
                                         (wp,uu____3269)::[])
                                        -> (t1, res, wp, g)
                                    | uu____3312 -> failwith "Impossible")
                                in
                             (match uu____3159 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____3343 =
                                    let uu____3348 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____3348 with
                                    | (e2,c,g) ->
                                        ((let uu____3363 =
                                            let uu____3364 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____3364
                                             in
                                          if uu____3363
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____3374 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____3374 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____3382 =
                                                  let uu____3389 =
                                                    let uu____3394 =
                                                      let uu____3395 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____3396 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____3395 uu____3396
                                                       in
                                                    (uu____3394,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____3389]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____3382);
                                               (let uu____3405 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____3405)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____3407 =
                                                let uu____3408 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____3408
                                                 in
                                              (e2, uu____3407)))
                                     in
                                  (match uu____3343 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____3418 =
                                           let uu____3419 =
                                             let uu____3420 =
                                               let uu____3421 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____3421]  in
                                             let uu____3422 =
                                               let uu____3431 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____3431]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____3420;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____3422;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____3419
                                            in
                                         FStar_All.pipe_right uu____3418
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____3451 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____3451 with
                                        | (e4,c1,g') ->
                                            let uu____3467 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____3467))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____3514 =
               let uu____3515 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____3515 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____3514 instantiate_both  in
           ((let uu____3531 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____3531
             then
               let uu____3532 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____3533 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____3532
                 uu____3533
             else ());
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.quote_lid
                   -> true
               | uu____3537 -> false  in
             let uu____3538 = tc_term (no_inst env2) head1  in
             match uu____3538 with
             | (head2,chead,g_head) ->
                 let uu____3554 =
                   let uu____3561 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____3561
                   then
                     let uu____3568 =
                       let uu____3575 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____3575
                        in
                     match uu____3568 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____3588 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____3590 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c
                                    in
                                 Prims.op_Negation uu____3590))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                              in
                           if uu____3588
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c  in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2  in
                      let uu____3595 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env3 head2 chead g_head args
                        uu____3595)
                    in
                 (match uu____3554 with
                  | (e1,c,g) ->
                      ((let uu____3608 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____3608
                        then
                          let uu____3609 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____3609
                        else ());
                       (let uu____3611 = comp_check_expected_typ env0 e1 c
                           in
                        match uu____3611 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____3628 =
                                let uu____3629 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____3629.FStar_Syntax_Syntax.n  in
                              match uu____3628 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____3633) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___97_3695 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___97_3695.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___97_3695.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___97_3695.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____3744 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____3746 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____3746
                               in
                            ((let uu____3748 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____3748
                              then
                                let uu____3749 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____3750 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____3749 uu____3750
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____3790 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____3790 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____3810 = tc_term env12 e1  in
                (match uu____3810 with
                 | (e11,c1,g1) ->
                     let uu____3826 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____3836 = FStar_Syntax_Util.type_u ()  in
                           (match uu____3836 with
                            | (k,uu____3846) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k  in
                                let uu____3848 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t
                                   in
                                (uu____3848, res_t))
                        in
                     (match uu____3826 with
                      | (env_branches,res_t) ->
                          ((let uu____3858 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____3858
                            then
                              let uu____3859 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____3859
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____3945 =
                              let uu____3950 =
                                FStar_List.fold_right
                                  (fun uu____3996  ->
                                     fun uu____3997  ->
                                       match (uu____3996, uu____3997) with
                                       | ((uu____4060,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4120 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), uu____4120))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____3950 with
                              | (cases,g) ->
                                  let uu____4159 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____4159, g)
                               in
                            match uu____3945 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (FStar_Pervasives_Native.Some e11) c1
                                    ((FStar_Pervasives_Native.Some guard_x),
                                      c_branches)
                                   in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____4255  ->
                                              match uu____4255 with
                                              | ((pat,wopt,br),uu____4283,lc,uu____4285)
                                                  ->
                                                  let uu____4298 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  (pat, wopt, uu____4298)))
                                       in
                                    let e2 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_match
                                           (scrutinee, branches))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let e3 =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env1 e2
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e3,
                                           ((FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                             FStar_Pervasives_Native.None),
                                           (FStar_Pervasives_Native.Some
                                              (cres.FStar_Syntax_Syntax.eff_name))))
                                      FStar_Pervasives_Native.None
                                      e3.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____4353 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____4353
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____4360 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____4360  in
                                     let lb =
                                       let uu____4364 =
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
                                           uu____4364;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       }  in
                                     let e2 =
                                       let uu____4368 =
                                         let uu____4371 =
                                           let uu____4372 =
                                             let uu____4385 =
                                               let uu____4386 =
                                                 let uu____4387 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____4387]  in
                                               FStar_Syntax_Subst.close
                                                 uu____4386 e_match
                                                in
                                             ((false, [lb]), uu____4385)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____4372
                                            in
                                         FStar_Syntax_Syntax.mk uu____4371
                                          in
                                       uu____4368
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____4400 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____4400
                                  then
                                    let uu____4401 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____4402 =
                                      let uu____4403 =
                                        cres.FStar_Syntax_Syntax.comp ()  in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____4403
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____4401 uu____4402
                                  else ());
                                 (let uu____4405 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e2, cres, uu____4405))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____4408;
                FStar_Syntax_Syntax.lbunivs = uu____4409;
                FStar_Syntax_Syntax.lbtyp = uu____4410;
                FStar_Syntax_Syntax.lbeff = uu____4411;
                FStar_Syntax_Syntax.lbdef = uu____4412;_}::[]),uu____4413)
           ->
           ((let uu____4433 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____4433
             then
               let uu____4434 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____4434
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____4436),uu____4437) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____4452;
                FStar_Syntax_Syntax.lbunivs = uu____4453;
                FStar_Syntax_Syntax.lbtyp = uu____4454;
                FStar_Syntax_Syntax.lbeff = uu____4455;
                FStar_Syntax_Syntax.lbdef = uu____4456;_}::uu____4457),uu____4458)
           ->
           ((let uu____4480 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____4480
             then
               let uu____4481 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____4481
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____4483),uu____4484) ->
           check_inner_let_rec env1 top)

and tc_synth :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun args  ->
      fun rng  ->
        let uu____4510 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____4600))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____4660))::(uu____4661,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____4662))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____4735 ->
              FStar_Exn.raise
                (FStar_Errors.Error ("synth_by_tactic: bad application", rng))
           in
        match uu____4510 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____4819 = FStar_TypeChecker_Env.expected_typ env  in
                  (match uu____4819 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____4825 =
                         let uu____4826 =
                           let uu____4831 =
                             FStar_TypeChecker_Env.get_range env  in
                           ("synth_by_tactic: need a type annotation when no expected type is present",
                             uu____4831)
                            in
                         FStar_Errors.Error uu____4826  in
                       FStar_Exn.raise uu____4825)
               in
            let uu____4834 = FStar_TypeChecker_Env.clear_expected_typ env  in
            (match uu____4834 with
             | (env',uu____4848) ->
                 let uu____4853 = tc_term env' typ  in
                 (match uu____4853 with
                  | (typ1,uu____4867,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____4870 = tc_term env' tau  in
                        match uu____4870 with
                        | (tau1,c,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let uu____4888 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Tac")
                                 in
                              if uu____4888
                              then
                                let uu____4889 =
                                  FStar_Syntax_Print.term_to_string tau1  in
                                let uu____4890 =
                                  FStar_Syntax_Print.term_to_string typ1  in
                                FStar_Util.print2
                                  "Running tactic %s at return type %s\n"
                                  uu____4889 uu____4890
                              else ());
                             (let t =
                                env.FStar_TypeChecker_Env.synth env' typ1
                                  tau1
                                 in
                              (let uu____4894 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Tac")
                                  in
                               if uu____4894
                               then
                                 let uu____4895 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 FStar_Util.print1 "Got %s\n" uu____4895
                               else ());
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____4898 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng
                                  in
                               tc_term env uu____4898)))))))

and tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some tactic ->
          let uu____4914 =
            tc_check_tot_or_gtot_term env tactic
              FStar_Syntax_Syntax.t_tactic_unit
             in
          (match uu____4914 with
           | (tactic1,uu____4924,uu____4925) ->
               FStar_Pervasives_Native.Some tactic1)

and tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____4964 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____4964 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____4985 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____4985
              then FStar_Util.Inl t1
              else
                (let uu____4991 =
                   let uu____4992 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____4992
                    in
                 FStar_Util.Inr uu____4991)
               in
            let is_data_ctor uu___86_5002 =
              match uu___86_5002 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____5005) -> true
              | uu____5012 -> false  in
            let uu____5015 =
              (is_data_ctor dc) &&
                (let uu____5017 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____5017)
               in
            if uu____5015
            then
              let uu____5024 =
                let uu____5025 =
                  let uu____5030 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  let uu____5031 = FStar_TypeChecker_Env.get_range env1  in
                  (uu____5030, uu____5031)  in
                FStar_Errors.Error uu____5025  in
              FStar_Exn.raise uu____5024
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____5048 =
            let uu____5049 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____5049
             in
          failwith uu____5048
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____5083 =
              let uu____5084 = FStar_Syntax_Subst.compress t1  in
              uu____5084.FStar_Syntax_Syntax.n  in
            match uu____5083 with
            | FStar_Syntax_Syntax.Tm_arrow uu____5087 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____5100 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___98_5138 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___98_5138.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___98_5138.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___98_5138.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____5190 =
            let uu____5203 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____5203 with
            | FStar_Pervasives_Native.None  ->
                let uu____5218 = FStar_Syntax_Util.type_u ()  in
                (match uu____5218 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard)
             in
          (match uu____5190 with
           | (t,uu____5255,g0) ->
               let uu____5269 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____5269 with
                | (e1,uu____5289,g1) ->
                    let uu____5303 =
                      let uu____5304 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____5304
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____5305 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____5303, uu____5305)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____5307 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____5320 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____5320)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____5307 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___99_5339 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___99_5339.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___99_5339.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.bv
                  x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____5342 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____5342 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____5363 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____5363
                       then FStar_Util.Inl t1
                       else
                         (let uu____5369 =
                            let uu____5370 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____5370
                             in
                          FStar_Util.Inr uu____5369)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____5376;
             FStar_Syntax_Syntax.vars = uu____5377;_},uu____5378)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____5383 =
            let uu____5384 =
              let uu____5389 = FStar_TypeChecker_Env.get_range env1  in
              ("Badly instantiated synth_by_tactic", uu____5389)  in
            FStar_Errors.Error uu____5384  in
          FStar_Exn.raise uu____5383
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____5397 =
            let uu____5398 =
              let uu____5403 = FStar_TypeChecker_Env.get_range env1  in
              ("Badly instantiated synth_by_tactic", uu____5403)  in
            FStar_Errors.Error uu____5398  in
          FStar_Exn.raise uu____5397
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____5411;
             FStar_Syntax_Syntax.vars = uu____5412;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____5421 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5421 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____5444 =
                     let uu____5445 =
                       let uu____5450 =
                         let uu____5451 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____5452 =
                           FStar_Util.string_of_int (FStar_List.length us1)
                            in
                         let uu____5453 =
                           FStar_Util.string_of_int (FStar_List.length us')
                            in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____5451 uu____5452 uu____5453
                          in
                       let uu____5454 = FStar_TypeChecker_Env.get_range env1
                          in
                       (uu____5450, uu____5454)  in
                     FStar_Errors.Error uu____5445  in
                   FStar_Exn.raise uu____5444)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____5470 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.fv
                   fv' t;
                 (let e1 =
                    let uu____5474 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____5474 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5476 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5476 with
           | ((us,t),range) ->
               ((let uu____5499 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____5499
                 then
                   let uu____5500 =
                     let uu____5501 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____5501  in
                   let uu____5502 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____5503 = FStar_Range.string_of_range range  in
                   let uu____5504 = FStar_Range.string_of_use_range range  in
                   let uu____5505 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____5500 uu____5502 uu____5503 uu____5504 uu____5505
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.fv
                   fv' t;
                 (let e1 =
                    let uu____5510 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____5510 us  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____5534 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____5534 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____5548 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____5548 with
                | (env2,uu____5562) ->
                    let uu____5567 = tc_binders env2 bs1  in
                    (match uu____5567 with
                     | (bs2,env3,g,us) ->
                         let uu____5586 = tc_comp env3 c1  in
                         (match uu____5586 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___100_5605 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___100_5605.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___100_5605.FStar_Syntax_Syntax.vars)
                                }  in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us)
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos
                                   in
                                let g1 =
                                  let uu____5614 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____5614
                                   in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u  in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
             in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____5633 =
            let uu____5638 =
              let uu____5639 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____5639]  in
            FStar_Syntax_Subst.open_term uu____5638 phi  in
          (match uu____5633 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____5649 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____5649 with
                | (env2,uu____5663) ->
                    let uu____5668 =
                      let uu____5681 = FStar_List.hd x1  in
                      tc_binder env2 uu____5681  in
                    (match uu____5668 with
                     | (x2,env3,f1,u) ->
                         ((let uu____5709 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____5709
                           then
                             let uu____5710 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____5711 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____5712 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____5710 uu____5711 uu____5712
                           else ());
                          (let uu____5714 = FStar_Syntax_Util.type_u ()  in
                           match uu____5714 with
                           | (t_phi,uu____5726) ->
                               let uu____5727 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____5727 with
                                | (phi2,uu____5741,f2) ->
                                    let e1 =
                                      let uu___101_5746 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___101_5746.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___101_5746.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____5753 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____5753
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5766) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____5789 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____5789
            then
              let uu____5790 =
                FStar_Syntax_Print.term_to_string
                  (let uu___102_5793 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___102_5793.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___102_5793.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____5790
            else ());
           (let uu____5799 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____5799 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____5812 ->
          let uu____5813 =
            let uu____5814 = FStar_Syntax_Print.term_to_string top  in
            let uu____5815 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____5814
              uu____5815
             in
          failwith uu____5813

and tc_constant :
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
      | FStar_Const.Const_bool uu____5824 -> FStar_Syntax_Util.t_bool
      | FStar_Const.Const_int (uu____5825,FStar_Pervasives_Native.None ) ->
          FStar_Syntax_Syntax.t_int
      | FStar_Const.Const_int
          (uu____5836,FStar_Pervasives_Native.Some uu____5837) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____5852 -> FStar_Syntax_Syntax.t_string
      | FStar_Const.Const_float uu____5859 -> FStar_Syntax_Syntax.t_float
      | FStar_Const.Const_char uu____5860 -> FStar_Syntax_Syntax.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____5861 -> FStar_Syntax_Syntax.t_range
      | uu____5862 ->
          FStar_Exn.raise (FStar_Errors.Error ("Unsupported constant", r))

and tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.universe,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun c  ->
      let c0 = c  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____5879) ->
          let uu____5888 = FStar_Syntax_Util.type_u ()  in
          (match uu____5888 with
           | (k,u) ->
               let uu____5901 = tc_check_tot_or_gtot_term env t k  in
               (match uu____5901 with
                | (t1,uu____5915,g) ->
                    let uu____5917 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____5917, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____5919) ->
          let uu____5928 = FStar_Syntax_Util.type_u ()  in
          (match uu____5928 with
           | (k,u) ->
               let uu____5941 = tc_check_tot_or_gtot_term env t k  in
               (match uu____5941 with
                | (t1,uu____5955,g) ->
                    let uu____5957 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____5957, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____5965 =
              let uu____5966 =
                let uu____5967 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____5967 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____5966  in
            uu____5965 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____5970 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____5970 with
           | (tc1,uu____5984,f) ->
               let uu____5986 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____5986 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____6030 =
                        let uu____6031 = FStar_Syntax_Subst.compress head3
                           in
                        uu____6031.FStar_Syntax_Syntax.n  in
                      match uu____6030 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____6034,us) -> us
                      | uu____6040 -> []  in
                    let uu____6041 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____6041 with
                     | (uu____6062,args1) ->
                         let uu____6084 =
                           let uu____6103 = FStar_List.hd args1  in
                           let uu____6116 = FStar_List.tl args1  in
                           (uu____6103, uu____6116)  in
                         (match uu____6084 with
                          | (res,args2) ->
                              let uu____6181 =
                                let uu____6190 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___87_6218  ->
                                          match uu___87_6218 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____6226 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____6226 with
                                               | (env1,uu____6238) ->
                                                   let uu____6243 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____6243 with
                                                    | (e1,uu____6255,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____6190
                                  FStar_List.unzip
                                 in
                              (match uu____6181 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___103_6294 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___103_6294.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___103_6294.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____6298 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____6298 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____6302 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____6302))))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____6310 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____6311 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____6321 = aux u3  in FStar_Syntax_Syntax.U_succ uu____6321
        | FStar_Syntax_Syntax.U_max us ->
            let uu____6325 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____6325
        | FStar_Syntax_Syntax.U_name x -> u2  in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____6330 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____6330 FStar_Pervasives_Native.snd
         | uu____6339 -> aux u)

and tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail msg t =
            let uu____6363 =
              let uu____6364 =
                let uu____6369 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top
                   in
                (uu____6369, (top.FStar_Syntax_Syntax.pos))  in
              FStar_Errors.Error uu____6364  in
            FStar_Exn.raise uu____6363  in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____6459 bs2 bs_expected1 =
              match uu____6459 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____6627)) ->
                             let uu____6632 =
                               let uu____6633 =
                                 let uu____6638 =
                                   let uu____6639 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____6639
                                    in
                                 let uu____6640 =
                                   FStar_Syntax_Syntax.range_of_bv hd1  in
                                 (uu____6638, uu____6640)  in
                               FStar_Errors.Error uu____6633  in
                             FStar_Exn.raise uu____6632
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____6641),FStar_Pervasives_Native.None ) ->
                             let uu____6646 =
                               let uu____6647 =
                                 let uu____6652 =
                                   let uu____6653 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____6653
                                    in
                                 let uu____6654 =
                                   FStar_Syntax_Syntax.range_of_bv hd1  in
                                 (uu____6652, uu____6654)  in
                               FStar_Errors.Error uu____6647  in
                             FStar_Exn.raise uu____6646
                         | uu____6655 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____6661 =
                           let uu____6666 =
                             let uu____6667 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____6667.FStar_Syntax_Syntax.n  in
                           match uu____6666 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____6674 ->
                               ((let uu____6676 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____6676
                                 then
                                   let uu____6677 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____6677
                                 else ());
                                (let uu____6679 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____6679 with
                                 | (t,uu____6691,g1) ->
                                     let g2 =
                                       let uu____6694 =
                                         FStar_TypeChecker_Env.get_range env2
                                          in
                                       let uu____6695 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t
                                          in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____6694
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____6695
                                        in
                                     let g3 =
                                       let uu____6697 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____6697
                                        in
                                     (t, g3)))
                            in
                         match uu____6661 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___104_6725 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___104_6725.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___104_6725.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____6738 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____6738
                                in
                             aux (env3, (b :: out), g1, subst2) bs3
                               bs_expected2))
                   | (rest,[]) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         g, subst1)
                   | ([],rest) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         g, subst1))
               in
            aux (env1, [], FStar_TypeChecker_Rel.trivial_guard, []) bs1
              bs_expected
             in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____6900 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____6907 = tc_binders env1 bs  in
                  match uu____6907 with
                  | (bs1,envbody,g,uu____6945) ->
                      let uu____6946 =
                        let uu____6959 =
                          let uu____6960 = FStar_Syntax_Subst.compress body1
                             in
                          uu____6960.FStar_Syntax_Syntax.n  in
                        match uu____6959 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____6978) ->
                            let uu____7025 = tc_comp envbody c  in
                            (match uu____7025 with
                             | (c1,uu____7045,g') ->
                                 let uu____7047 =
                                   tc_tactic_opt envbody tacopt  in
                                 let uu____7050 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((FStar_Pervasives_Native.Some c1),
                                   uu____7047, body1, uu____7050))
                        | uu____7055 ->
                            (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None, body1, g)
                         in
                      (match uu____6946 with
                       | (copt,tacopt,body2,g1) ->
                           (FStar_Pervasives_Native.None, bs1, [], copt,
                             tacopt, envbody, body2, g1))))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____7159 =
                    let uu____7160 = FStar_Syntax_Subst.compress t2  in
                    uu____7160.FStar_Syntax_Syntax.n  in
                  match uu____7159 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____7191 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____7213 -> failwith "Impossible");
                       (let uu____7220 = tc_binders env1 bs  in
                        match uu____7220 with
                        | (bs1,envbody,g,uu____7260) ->
                            let uu____7261 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____7261 with
                             | (envbody1,uu____7297) ->
                                 ((FStar_Pervasives_Native.Some (t2, true)),
                                   bs1, [], FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____7318;
                         FStar_Syntax_Syntax.pos = uu____7319;
                         FStar_Syntax_Syntax.vars = uu____7320;_},uu____7321)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____7363 -> failwith "Impossible");
                       (let uu____7370 = tc_binders env1 bs  in
                        match uu____7370 with
                        | (bs1,envbody,g,uu____7410) ->
                            let uu____7411 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____7411 with
                             | (envbody1,uu____7447) ->
                                 ((FStar_Pervasives_Native.Some (t2, true)),
                                   bs1, [], FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____7469) ->
                      let uu____7474 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____7474 with
                       | (uu____7531,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some (t2, false)), bs1,
                             bs', copt, tacopt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____7597 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____7597 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____7705 c_expected2 =
                               match uu____7705 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____7820 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____7820)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____7851 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____7851
                                           in
                                        let uu____7852 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____7852)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
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
                                               let uu____7924 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____7924 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____7945 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____7945 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____7993 =
                                                           let uu____8024 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____8024,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____7993
                                                           c_expected4))
                                           | uu____8041 ->
                                               let uu____8042 =
                                                 let uu____8043 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3
                                                    in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____8043
                                                  in
                                               fail uu____8042 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2)
                                in
                             let uu____8073 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____8073 c_expected1  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___105_8132 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___105_8132.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___105_8132.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___105_8132.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___105_8132.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___105_8132.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___105_8132.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___105_8132.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___105_8132.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___105_8132.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___105_8132.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___105_8132.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___105_8132.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___105_8132.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___105_8132.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___105_8132.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___105_8132.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___105_8132.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___105_8132.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___105_8132.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___105_8132.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___105_8132.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___105_8132.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___105_8132.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___105_8132.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___105_8132.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___105_8132.FStar_TypeChecker_Env.is_native_tactic)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____8171  ->
                                     fun uu____8172  ->
                                       match (uu____8171, uu____8172) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____8217 =
                                             let uu____8224 =
                                               let uu____8225 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8225
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____8224 t3  in
                                           (match uu____8217 with
                                            | (t4,uu____8247,uu____8248) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____8258 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___106_8261
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___106_8261.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___106_8261.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____8258 ::
                                                        letrec_binders
                                                  | uu____8262 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____8267 =
                             check_actuals_against_formals env1 bs
                               bs_expected1
                              in
                           (match uu____8267 with
                            | (envbody,bs1,g,c) ->
                                let uu____8326 =
                                  let uu____8333 =
                                    FStar_TypeChecker_Env.should_verify env1
                                     in
                                  if uu____8333
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, [])  in
                                (match uu____8326 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((FStar_Pervasives_Native.Some
                                         (t2, false)), bs1, letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       FStar_Pervasives_Native.None,
                                       envbody2, body1, g))))
                  | uu____8400 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____8429 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____8429
                      else
                        (let uu____8431 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____8431 with
                         | (uu____8486,bs1,uu____8488,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some (t2, false)),
                               bs1, [], c_opt, tacopt, envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____8531 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____8531 with
          | (env1,topt) ->
              ((let uu____8551 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____8551
                then
                  let uu____8552 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____8552
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____8556 = expected_function_typ1 env1 topt body  in
                match uu____8556 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____8617 =
                      tc_term
                        (let uu___107_8626 = envbody  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___107_8626.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___107_8626.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___107_8626.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___107_8626.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___107_8626.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___107_8626.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___107_8626.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___107_8626.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___107_8626.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___107_8626.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___107_8626.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___107_8626.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___107_8626.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___107_8626.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___107_8626.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___107_8626.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___107_8626.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___107_8626.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___107_8626.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___107_8626.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___107_8626.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___107_8626.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___107_8626.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___107_8626.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___107_8626.FStar_TypeChecker_Env.is_native_tactic)
                         }) body1
                       in
                    (match uu____8617 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         ((let uu____8638 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits")
                              in
                           if uu____8638
                           then
                             let uu____8639 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits)
                                in
                             let uu____8652 =
                               let uu____8653 =
                                 cbody.FStar_Syntax_Syntax.comp ()  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____8653
                                in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____8639 uu____8652
                           else ());
                          (let uu____8655 =
                             let uu____8662 =
                               let uu____8667 =
                                 cbody.FStar_Syntax_Syntax.comp ()  in
                               (body2, uu____8667)  in
                             check_expected_effect
                               (let uu___108_8674 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___108_8674.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___108_8674.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___108_8674.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___108_8674.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___108_8674.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___108_8674.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___108_8674.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___108_8674.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___108_8674.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___108_8674.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___108_8674.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___108_8674.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___108_8674.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___108_8674.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___108_8674.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___108_8674.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___108_8674.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___108_8674.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___108_8674.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___108_8674.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___108_8674.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___108_8674.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___108_8674.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___108_8674.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___108_8674.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___108_8674.FStar_TypeChecker_Env.is_native_tactic)
                                }) c_opt uu____8662
                              in
                           match uu____8655 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard
                                  in
                               let guard2 =
                                 let uu____8686 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____8688 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1
                                         in
                                      Prims.op_Negation uu____8688)
                                    in
                                 if uu____8686
                                 then
                                   let uu____8689 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1
                                      in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____8689
                                 else
                                   (let guard2 =
                                      let uu____8692 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1
                                         in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____8692
                                       in
                                    guard2)
                                  in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1  in
                               let e =
                                 FStar_Syntax_Util.abs bs1 body3
                                   (FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         (FStar_Util.dflt cbody1 c_opt)))
                                  in
                               let uu____8701 =
                                 match tfun_opt with
                                 | FStar_Pervasives_Native.Some (t,use_teq)
                                     ->
                                     let t1 = FStar_Syntax_Subst.compress t
                                        in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____8727 -> (e, t1, guard2)
                                      | uu____8740 ->
                                          let uu____8741 =
                                            if use_teq
                                            then
                                              let uu____8750 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed
                                                 in
                                              (e, uu____8750)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1
                                             in
                                          (match uu____8741 with
                                           | (e1,guard') ->
                                               let uu____8760 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard'
                                                  in
                                               (e1, t1, uu____8760)))
                                 | FStar_Pervasives_Native.None  ->
                                     (e, tfun_computed, guard2)
                                  in
                               (match uu____8701 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1
                                       in
                                    let uu____8778 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        FStar_Pervasives_Native.None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3
                                       in
                                    (match uu____8778 with
                                     | (c1,g1) -> (e1, c1, g1))))))))

and check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3
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
              (let uu____8827 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____8827
               then
                 let uu____8828 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____8829 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____8828
                   uu____8829
               else ());
              (let monadic_application uu____8886 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____8886 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres1 =
                       let uu___109_8945 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___109_8945.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___109_8945.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___109_8945.FStar_Syntax_Syntax.comp)
                       }  in
                     let uu____8946 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1
                              in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard
                              in
                           (cres2, g)
                       | uu____8961 ->
                           let g =
                             let uu____8969 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard
                                in
                             FStar_All.pipe_right uu____8969
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____8970 =
                             let uu____8971 =
                               let uu____8974 =
                                 let uu____8975 =
                                   let uu____8976 =
                                     cres1.FStar_Syntax_Syntax.comp ()  in
                                   FStar_Syntax_Util.arrow bs uu____8976  in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____8975
                                  in
                               FStar_Syntax_Syntax.mk_Total uu____8974  in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____8971
                              in
                           (uu____8970, g)
                        in
                     (match uu____8946 with
                      | (cres2,guard1) ->
                          ((let uu____8990 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____8990
                            then
                              let uu____8991 =
                                FStar_Syntax_Print.lcomp_to_string cres2  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____8991
                            else ());
                           (let cres3 =
                              let uu____8994 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2
                                 in
                              if uu____8994
                              then
                                let term =
                                  FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets_rev)
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos
                                   in
                                FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                  env term cres2
                              else cres2  in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____9028  ->
                                     match uu____9028 with
                                     | ((e,q),x,c) ->
                                         let uu____9061 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____9061
                                         then
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             (FStar_Pervasives_Native.Some e)
                                             c (x, out_c)
                                         else
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             FStar_Pervasives_Native.None c
                                             (x, out_c)) cres3 arg_comps_rev
                               in
                            let comp1 =
                              FStar_TypeChecker_Util.bind
                                head2.FStar_Syntax_Syntax.pos env
                                FStar_Pervasives_Native.None chead1
                                (FStar_Pervasives_Native.None, comp)
                               in
                            let shortcuts_evaluation_order =
                              let uu____9073 =
                                let uu____9074 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____9074.FStar_Syntax_Syntax.n  in
                              match uu____9073 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____9078 -> false  in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____9099  ->
                                         match uu____9099 with
                                         | (arg,uu____9113,uu____9114) -> arg
                                             :: args1) [] arg_comps_rev
                                   in
                                let app =
                                  FStar_Syntax_Syntax.mk_Tm_app head2 args1
                                    FStar_Pervasives_Native.None r
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
                                (let uu____9124 =
                                   let map_fun uu____9186 =
                                     match uu____9186 with
                                     | ((e,q),uu____9221,c) ->
                                         let uu____9231 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____9231
                                         then
                                           (FStar_Pervasives_Native.None,
                                             (e, q))
                                         else
                                           (let x =
                                              FStar_Syntax_Syntax.new_bv
                                                FStar_Pervasives_Native.None
                                                c.FStar_Syntax_Syntax.res_typ
                                               in
                                            let e1 =
                                              FStar_TypeChecker_Util.maybe_lift
                                                env e
                                                c.FStar_Syntax_Syntax.eff_name
                                                comp1.FStar_Syntax_Syntax.eff_name
                                                c.FStar_Syntax_Syntax.res_typ
                                               in
                                            let uu____9281 =
                                              let uu____9286 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              (uu____9286, q)  in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____9281))
                                      in
                                   let uu____9315 =
                                     let uu____9340 =
                                       let uu____9363 =
                                         let uu____9378 =
                                           let uu____9387 =
                                             FStar_Syntax_Syntax.as_arg head2
                                              in
                                           (uu____9387,
                                             FStar_Pervasives_Native.None,
                                             chead1)
                                            in
                                         uu____9378 :: arg_comps_rev  in
                                       FStar_List.map map_fun uu____9363  in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____9340
                                      in
                                   match uu____9315 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____9560 =
                                         let uu____9561 =
                                           FStar_List.hd reverse_args  in
                                         FStar_Pervasives_Native.fst
                                           uu____9561
                                          in
                                       let uu____9570 =
                                         let uu____9577 =
                                           FStar_List.tl reverse_args  in
                                         FStar_List.rev uu____9577  in
                                       (lifted_args, uu____9560, uu____9570)
                                    in
                                 match uu____9124 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head3
                                         args1 FStar_Pervasives_Native.None r
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
                                     let bind_lifted_args e uu___88_9680 =
                                       match uu___88_9680 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1
                                              in
                                           let letbinding =
                                             let uu____9735 =
                                               let uu____9738 =
                                                 let uu____9739 =
                                                   let uu____9752 =
                                                     let uu____9753 =
                                                       let uu____9754 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____9754]  in
                                                     FStar_Syntax_Subst.close
                                                       uu____9753 e
                                                      in
                                                   ((false, [lb]),
                                                     uu____9752)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____9739
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____9738
                                                in
                                             uu____9735
                                               FStar_Pervasives_Native.None
                                               e.FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_meta
                                                (letbinding,
                                                  (FStar_Syntax_Syntax.Meta_monadic
                                                     (m,
                                                       (comp1.FStar_Syntax_Syntax.res_typ)))))
                                             FStar_Pervasives_Native.None
                                             e.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args)
                               in
                            let uu____9784 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1
                               in
                            match uu____9784 with
                            | (comp2,g) -> (app, comp2, g))))
                  in
               let rec tc_args head_info uu____9875 bs args1 =
                 match uu____9875 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____10022))::rest,
                         (uu____10024,FStar_Pervasives_Native.None )::uu____10025)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          let uu____10086 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____10086 with
                           | (varg,uu____10106,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1
                                  in
                               let arg =
                                 let uu____10128 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____10128)  in
                               let uu____10129 =
                                 let uu____10164 =
                                   let uu____10179 =
                                     let uu____10192 =
                                       let uu____10193 =
                                         FStar_Syntax_Syntax.mk_Total t1  in
                                       FStar_All.pipe_right uu____10193
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____10192)
                                      in
                                   uu____10179 :: outargs  in
                                 let uu____10212 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst2, uu____10164, (arg :: arg_rets),
                                   uu____10212, fvs)
                                  in
                               tc_args head_info uu____10129 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____10314),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____10315)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____10328 ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___110_10339 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___110_10339.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___110_10339.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____10341 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____10341
                             then
                               let uu____10342 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____10342
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1
                                in
                             let env2 =
                               let uu___111_10347 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___111_10347.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___111_10347.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___111_10347.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___111_10347.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___111_10347.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___111_10347.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___111_10347.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___111_10347.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___111_10347.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___111_10347.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___111_10347.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___111_10347.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___111_10347.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___111_10347.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___111_10347.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___111_10347.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___111_10347.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___111_10347.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___111_10347.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___111_10347.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___111_10347.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___111_10347.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___111_10347.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___111_10347.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___111_10347.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___111_10347.FStar_TypeChecker_Env.is_native_tactic)
                               }  in
                             (let uu____10349 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High
                                 in
                              if uu____10349
                              then
                                let uu____10350 =
                                  FStar_Syntax_Print.tag_of_term e  in
                                let uu____10351 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____10352 =
                                  FStar_Syntax_Print.term_to_string targ1  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____10350 uu____10351 uu____10352
                              else ());
                             (let uu____10354 = tc_term env2 e  in
                              match uu____10354 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e1, aq)  in
                                  let xterm =
                                    let uu____10381 =
                                      FStar_Syntax_Syntax.bv_to_name x1  in
                                    FStar_Syntax_Syntax.as_arg uu____10381
                                     in
                                  let uu____10382 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name)
                                     in
                                  if uu____10382
                                  then
                                    let subst2 =
                                      let uu____10390 = FStar_List.hd bs  in
                                      maybe_extend_subst subst1 uu____10390
                                        e1
                                       in
                                    tc_args head_info
                                      (subst2,
                                        ((arg,
                                           (FStar_Pervasives_Native.Some x1),
                                           c) :: outargs), (xterm ::
                                        arg_rets), g1, fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1,
                                        ((arg,
                                           (FStar_Pervasives_Native.Some x1),
                                           c) :: outargs), (xterm ::
                                        arg_rets), g1, (x1 :: fvs)) rest
                                      rest'))))
                      | (uu____10484,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____10520) ->
                          let uu____10571 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____10571 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____10605 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____10605
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____10630 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____10630 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1))
                                             in
                                          ((let uu____10653 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____10653
                                            then
                                              let uu____10654 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____10654
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____10696 when Prims.op_Negation norm1
                                     ->
                                     let uu____10697 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1
                                        in
                                     aux true uu____10697
                                 | uu____10698 ->
                                     let uu____10699 =
                                       let uu____10700 =
                                         let uu____10705 =
                                           let uu____10706 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead
                                              in
                                           let uu____10707 =
                                             FStar_Util.string_of_int n_args
                                              in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____10706 uu____10707
                                            in
                                         let uu____10714 =
                                           FStar_Syntax_Syntax.argpos arg  in
                                         (uu____10705, uu____10714)  in
                                       FStar_Errors.Error uu____10700  in
                                     FStar_Exn.raise uu____10699
                                  in
                               aux false chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf =
                 let uu____10733 =
                   let uu____10734 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____10734.FStar_Syntax_Syntax.n  in
                 match uu____10733 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____10745 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____10846 = tc_term env1 e  in
                           (match uu____10846 with
                            | (e1,c,g_e) ->
                                let uu____10868 = tc_args1 env1 tl1  in
                                (match uu____10868 with
                                 | (args2,comps,g_rest) ->
                                     let uu____10908 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____10908)))
                        in
                     let uu____10929 = tc_args1 env args  in
                     (match uu____10929 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____10966 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11004  ->
                                      match uu____11004 with
                                      | (uu____11017,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____10966
                             in
                          let ml_or_tot t r1 =
                            let uu____11034 = FStar_Options.ml_ish ()  in
                            if uu____11034
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____11037 =
                              let uu____11040 =
                                let uu____11041 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____11041
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_uvar env uu____11040
                               in
                            ml_or_tot uu____11037 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____11054 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____11054
                            then
                              let uu____11055 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____11056 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____11057 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11055 uu____11056 uu____11057
                            else ());
                           (let uu____11060 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11060);
                           (let comp =
                              let uu____11062 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____11073  ->
                                   fun out  ->
                                     match uu____11073 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11062
                               in
                            let uu____11087 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r
                               in
                            let uu____11090 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____11087, comp, uu____11090))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11093;
                        FStar_Syntax_Syntax.pos = uu____11094;
                        FStar_Syntax_Syntax.vars = uu____11095;_},uu____11096)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11217 = tc_term env1 e  in
                           (match uu____11217 with
                            | (e1,c,g_e) ->
                                let uu____11239 = tc_args1 env1 tl1  in
                                (match uu____11239 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11279 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11279)))
                        in
                     let uu____11300 = tc_args1 env args  in
                     (match uu____11300 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11337 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11375  ->
                                      match uu____11375 with
                                      | (uu____11388,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____11337
                             in
                          let ml_or_tot t r1 =
                            let uu____11405 = FStar_Options.ml_ish ()  in
                            if uu____11405
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____11408 =
                              let uu____11411 =
                                let uu____11412 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____11412
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_uvar env uu____11411
                               in
                            ml_or_tot uu____11408 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____11425 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____11425
                            then
                              let uu____11426 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____11427 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____11428 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11426 uu____11427 uu____11428
                            else ());
                           (let uu____11431 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11431);
                           (let comp =
                              let uu____11433 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____11444  ->
                                   fun out  ->
                                     match uu____11444 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11433
                               in
                            let uu____11458 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r
                               in
                            let uu____11461 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____11458, comp, uu____11461))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____11482 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____11482 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1))
                             in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____11547) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____11553,uu____11554) -> check_function_app t
                 | uu____11595 ->
                     let uu____11596 =
                       let uu____11597 =
                         let uu____11602 =
                           FStar_TypeChecker_Err.expected_function_typ env tf
                            in
                         (uu____11602, (head1.FStar_Syntax_Syntax.pos))  in
                       FStar_Errors.Error uu____11597  in
                     FStar_Exn.raise uu____11596
                  in
               check_function_app thead)

and check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3
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
                  let uu____11672 =
                    FStar_List.fold_left2
                      (fun uu____11715  ->
                         fun uu____11716  ->
                           fun uu____11717  ->
                             match (uu____11715, uu____11716, uu____11717)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____11785 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____11785 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____11803 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____11803 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____11807 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____11807)
                                              &&
                                              (let uu____11809 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____11809))
                                          in
                                       let uu____11810 =
                                         let uu____11819 =
                                           let uu____11828 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____11828]  in
                                         FStar_List.append seen uu____11819
                                          in
                                       let uu____11835 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____11810, uu____11835, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____11672 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____11871 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____11871
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____11873 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____11873 with | (c2,g) -> (e, c2, g)))
              | uu____11890 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 ->
        ((FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____11924 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____11924 with
        | (pattern,when_clause,branch_exp) ->
            let uu____11960 = branch1  in
            (match uu____11960 with
             | (cpat,uu____11992,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____12044 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                      in
                   match uu____12044 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____12073 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____12073
                         then
                           let uu____12074 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____12075 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12074 uu____12075
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____12078 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____12078 with
                         | (env1,uu____12098) ->
                             let env11 =
                               let uu___112_12104 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___112_12104.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___112_12104.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___112_12104.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___112_12104.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___112_12104.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___112_12104.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___112_12104.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___112_12104.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___112_12104.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___112_12104.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___112_12104.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___112_12104.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___112_12104.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___112_12104.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___112_12104.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___112_12104.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___112_12104.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___112_12104.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___112_12104.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___112_12104.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___112_12104.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___112_12104.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___112_12104.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___112_12104.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___112_12104.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___112_12104.FStar_TypeChecker_Env.is_native_tactic)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             ((let uu____12107 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High
                                  in
                               if uu____12107
                               then
                                 let uu____12108 =
                                   FStar_Syntax_Print.term_to_string exp  in
                                 let uu____12109 =
                                   FStar_Syntax_Print.term_to_string pat_t
                                    in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12108 uu____12109
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t
                                  in
                               let uu____12112 =
                                 tc_tot_or_gtot_term env12 exp  in
                               match uu____12112 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___113_12135 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___113_12135.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___113_12135.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___113_12135.FStar_TypeChecker_Env.implicits)
                                     }  in
                                   let uu____12136 =
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
                                     let uu____12140 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2
                                        in
                                     FStar_All.pipe_right uu____12140
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
                                   ((let uu____12157 =
                                       let uu____12158 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2
                                          in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____12158
                                        in
                                     if uu____12157
                                     then
                                       let unresolved =
                                         let uu____12170 =
                                           FStar_Util.set_difference uvs1
                                             uvs2
                                            in
                                         FStar_All.pipe_right uu____12170
                                           FStar_Util.set_elements
                                          in
                                       let uu____12197 =
                                         let uu____12198 =
                                           let uu____12203 =
                                             let uu____12204 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp
                                                in
                                             let uu____12205 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t
                                                in
                                             let uu____12206 =
                                               let uu____12207 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____12225  ->
                                                         match uu____12225
                                                         with
                                                         | (u,uu____12231) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____12207
                                                 (FStar_String.concat ", ")
                                                in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____12204 uu____12205
                                               uu____12206
                                              in
                                           (uu____12203,
                                             (p.FStar_Syntax_Syntax.p))
                                            in
                                         FStar_Errors.Error uu____12198  in
                                       FStar_Exn.raise uu____12197
                                     else ());
                                    (let uu____12236 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High
                                        in
                                     if uu____12236
                                     then
                                       let uu____12237 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1
                                          in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____12237
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
                 let uu____12246 =
                   let uu____12253 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____12253
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____12246 with
                  | (scrutinee_env,uu____12277) ->
                      let uu____12282 = tc_pat true pat_t pattern  in
                      (match uu____12282 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____12320 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____12342 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____12342
                                 then
                                   FStar_Exn.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____12356 =
                                      let uu____12363 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____12363 e  in
                                    match uu____12356 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____12320 with
                            | (when_clause1,g_when) ->
                                let uu____12397 = tc_term pat_env branch_exp
                                   in
                                (match uu____12397 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____12429 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40) uu____12429
                                        in
                                     let uu____12432 =
                                       let eqs =
                                         let uu____12442 =
                                           let uu____12443 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____12443  in
                                         if uu____12442
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp
                                               in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____12450 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____12467 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____12468 ->
                                                FStar_Pervasives_Native.None
                                            | uu____12469 ->
                                                let uu____12470 =
                                                  let uu____12471 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____12471 pat_t
                                                    scrutinee_tm e
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____12470)
                                          in
                                       let uu____12472 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch
                                          in
                                       match uu____12472 with
                                       | (c1,g_branch1) ->
                                           let uu____12487 =
                                             match (eqs, when_condition) with
                                             | uu____12500 when
                                                 let uu____12509 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____12509
                                                 -> (c1, g_when)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.None
                                                ) -> (c1, g_when)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.None
                                                ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf
                                                    in
                                                 let uu____12521 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____12522 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____12521, uu____12522)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____12531 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____12531
                                                    in
                                                 let uu____12532 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____12533 =
                                                   let uu____12534 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____12534 g_when
                                                    in
                                                 (uu____12532, uu____12533)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let uu____12542 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____12542, g_when)
                                              in
                                           (match uu____12487 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let uu____12554 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak
                                                   in
                                                let uu____12555 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak
                                                   in
                                                (uu____12554, uu____12555,
                                                  g_branch1))
                                        in
                                     (match uu____12432 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____12576 =
                                              let uu____12577 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____12577
                                               in
                                            if uu____12576
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____12607 =
                                                     let uu____12608 =
                                                       let uu____12609 =
                                                         let uu____12612 =
                                                           let uu____12619 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____12619
                                                            in
                                                         FStar_Pervasives_Native.snd
                                                           uu____12612
                                                          in
                                                       FStar_List.length
                                                         uu____12609
                                                        in
                                                     uu____12608 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____12607
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____12625 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____12625 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____12646 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         let disc1 =
                                                           let uu____12661 =
                                                             let uu____12662
                                                               =
                                                               let uu____12663
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____12663]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____12662
                                                              in
                                                           uu____12661
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____12666 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool
                                                            in
                                                         [uu____12666]
                                                   else []  in
                                                 let fail uu____12671 =
                                                   let uu____12672 =
                                                     let uu____12673 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____12674 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1
                                                        in
                                                     let uu____12675 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____12673
                                                       uu____12674
                                                       uu____12675
                                                      in
                                                   failwith uu____12672  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____12686) ->
                                                       head_constructor t1
                                                   | uu____12691 -> fail ()
                                                    in
                                                 let pat_exp2 =
                                                   let uu____12693 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____12693
                                                     FStar_Syntax_Util.unmeta
                                                    in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____12696 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____12713;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____12714;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____12715;_},uu____12716)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____12753 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____12755 =
                                                       let uu____12756 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____12756
                                                         scrutinee_tm1
                                                         pat_exp2
                                                        in
                                                     [uu____12755]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____12757 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____12765 =
                                                       let uu____12766 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____12766
                                                        in
                                                     if uu____12765
                                                     then []
                                                     else
                                                       (let uu____12770 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____12770)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____12773 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____12775 =
                                                       let uu____12776 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____12776
                                                        in
                                                     if uu____12775
                                                     then []
                                                     else
                                                       (let uu____12780 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____12780)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____12806 =
                                                       let uu____12807 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____12807
                                                        in
                                                     if uu____12806
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____12814 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____12846
                                                                     ->
                                                                    match uu____12846
                                                                    with
                                                                    | 
                                                                    (ei,uu____12856)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____12862
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____12862
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____12883
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____12897
                                                                    =
                                                                    let uu____12898
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____12899
                                                                    =
                                                                    let uu____12900
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____12900]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____12898
                                                                    uu____12899
                                                                     in
                                                                    uu____12897
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12814
                                                            FStar_List.flatten
                                                           in
                                                        let uu____12909 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____12909
                                                          sub_term_guards)
                                                 | uu____12912 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____12924 =
                                                   let uu____12925 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____12925
                                                    in
                                                 if uu____12924
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____12928 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____12928
                                                       in
                                                    let uu____12933 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____12933 with
                                                    | (k,uu____12939) ->
                                                        let uu____12940 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____12940
                                                         with
                                                         | (t1,uu____12948,uu____12949)
                                                             -> t1))
                                                  in
                                               let branch_guard =
                                                 build_and_check_branch_guard
                                                   scrutinee_tm norm_pat_exp
                                                  in
                                               let branch_guard1 =
                                                 match when_condition with
                                                 | FStar_Pervasives_Native.None
                                                      -> branch_guard
                                                 | FStar_Pervasives_Native.Some
                                                     w ->
                                                     FStar_Syntax_Util.mk_conj
                                                       branch_guard w
                                                  in
                                               branch_guard1)
                                             in
                                          let guard =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when1 g_branch1
                                             in
                                          ((let uu____12955 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____12955
                                            then
                                              let uu____12956 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____12956
                                            else ());
                                           (let uu____12958 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            (uu____12958, branch_guard, c1,
                                              guard)))))))))

and check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____12984 = check_let_bound_def true env1 lb  in
          (match uu____12984 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____13006 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13023 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____13023, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13026 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____13026
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____13030 =
                      let uu____13039 =
                        let uu____13050 =
                          let uu____13059 =
                            let uu____13072 = c1.FStar_Syntax_Syntax.comp ()
                               in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____13072)
                             in
                          [uu____13059]  in
                        FStar_TypeChecker_Util.generalize env1 uu____13050
                         in
                      FStar_List.hd uu____13039  in
                    match uu____13030 with
                    | (uu____13121,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11)))
                  in
               (match uu____13006 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____13135 =
                      let uu____13142 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____13142
                      then
                        let uu____13149 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____13149 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____13172 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.warn uu____13172
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____13173 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____13173, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____13183 = c11.FStar_Syntax_Syntax.comp ()
                               in
                            FStar_All.pipe_right uu____13183
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1)
                             in
                          let e21 =
                            let uu____13191 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____13191
                            then e2
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta
                                   (e2,
                                     (FStar_Syntax_Syntax.Meta_desugared
                                        FStar_Syntax_Syntax.Masked_effect)))
                                FStar_Pervasives_Native.None
                                e2.FStar_Syntax_Syntax.pos
                             in
                          (e21, c)))
                       in
                    (match uu____13135 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_Syntax_Syntax.t_unit
                            in
                         let lb1 =
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             lb.FStar_Syntax_Syntax.lbname univ_vars2
                             (FStar_Syntax_Util.comp_result c12)
                             (FStar_Syntax_Util.comp_effect_name c12) e11
                            in
                         let uu____13215 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         (uu____13215,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____13230 -> failwith "Impossible"

and check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___114_13261 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___114_13261.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___114_13261.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___114_13261.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___114_13261.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___114_13261.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___114_13261.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___114_13261.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___114_13261.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___114_13261.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___114_13261.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___114_13261.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___114_13261.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___114_13261.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___114_13261.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___114_13261.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___114_13261.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___114_13261.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___114_13261.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___114_13261.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___114_13261.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___114_13261.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___114_13261.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___114_13261.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___114_13261.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___114_13261.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___114_13261.FStar_TypeChecker_Env.is_native_tactic)
            }  in
          let uu____13262 =
            let uu____13273 =
              let uu____13274 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____13274 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____13273 lb  in
          (match uu____13262 with
           | (e1,uu____13296,c1,g1,annotated) ->
               let x =
                 let uu___115_13301 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___115_13301.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___115_13301.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 }  in
               let uu____13302 =
                 let uu____13307 =
                   let uu____13308 = FStar_Syntax_Syntax.mk_binder x  in
                   [uu____13308]  in
                 FStar_Syntax_Subst.open_term uu____13307 e2  in
               (match uu____13302 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb  in
                    let x1 = FStar_Pervasives_Native.fst xbinder  in
                    let uu____13327 =
                      let uu____13334 = FStar_TypeChecker_Env.push_bv env2 x1
                         in
                      tc_term uu____13334 e21  in
                    (match uu____13327 with
                     | (e22,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.bind
                             e1.FStar_Syntax_Syntax.pos env2
                             (FStar_Pervasives_Native.Some e1) c1
                             ((FStar_Pervasives_Native.Some x1), c2)
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
                           let uu____13353 =
                             let uu____13356 =
                               let uu____13357 =
                                 let uu____13370 =
                                   FStar_Syntax_Subst.close xb e23  in
                                 ((false, [lb1]), uu____13370)  in
                               FStar_Syntax_Syntax.Tm_let uu____13357  in
                             FStar_Syntax_Syntax.mk uu____13356  in
                           uu____13353 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ
                            in
                         let x_eq_e1 =
                           let uu____13384 =
                             let uu____13385 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ
                                in
                             let uu____13386 =
                               FStar_Syntax_Syntax.bv_to_name x1  in
                             FStar_Syntax_Util.mk_eq2 uu____13385
                               c1.FStar_Syntax_Syntax.res_typ uu____13386 e11
                              in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_TypeChecker_Common.NonTrivial _0_41)
                             uu____13384
                            in
                         let g21 =
                           let uu____13388 =
                             let uu____13389 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard uu____13389 g2
                              in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____13388
                            in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                            in
                         let uu____13391 =
                           let uu____13392 =
                             FStar_TypeChecker_Env.expected_typ env2  in
                           FStar_Option.isSome uu____13392  in
                         if uu____13391
                         then
                           let tt =
                             let uu____13402 =
                               FStar_TypeChecker_Env.expected_typ env2  in
                             FStar_All.pipe_right uu____13402
                               FStar_Option.get
                              in
                           ((let uu____13408 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____13408
                             then
                               let uu____13409 =
                                 FStar_Syntax_Print.term_to_string tt  in
                               let uu____13410 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____13409 uu____13410
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                               in
                            (let uu____13415 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____13415
                             then
                               let uu____13416 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               let uu____13417 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____13416 uu____13417
                             else ());
                            (e4,
                              ((let uu___116_13420 = cres  in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___116_13420.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___116_13420.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___116_13420.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____13421 -> failwith "Impossible"

and check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____13453 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____13453 with
           | (lbs1,e21) ->
               let uu____13472 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____13472 with
                | (env0,topt) ->
                    let uu____13491 = build_let_rec_env true env0 lbs1  in
                    (match uu____13491 with
                     | (lbs2,rec_env) ->
                         let uu____13510 = check_let_recs rec_env lbs2  in
                         (match uu____13510 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____13530 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____13530
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____13536 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____13536
                                  (fun _0_42  ->
                                     FStar_Pervasives_Native.Some _0_42)
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
                                     let uu____13581 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____13621 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____13621)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____13581
                                      in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____13661  ->
                                           match uu____13661 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e)))
                                 in
                              let cres =
                                let uu____13699 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____13699
                                 in
                              let uu____13704 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____13704 with
                               | (lbs5,e22) ->
                                   ((let uu____13724 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____13724
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____13725 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____13725, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____13738 -> failwith "Impossible"

and check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____13770 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____13770 with
           | (lbs1,e21) ->
               let uu____13789 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____13789 with
                | (env0,topt) ->
                    let uu____13808 = build_let_rec_env false env0 lbs1  in
                    (match uu____13808 with
                     | (lbs2,rec_env) ->
                         let uu____13827 = check_let_recs rec_env lbs2  in
                         (match uu____13827 with
                          | (lbs3,g_lbs) ->
                              let uu____13846 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___117_13869 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___117_13869.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___117_13869.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___118_13871 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___118_13871.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___118_13871.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___118_13871.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___118_13871.FStar_Syntax_Syntax.lbdef)
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
                              (match uu____13846 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____13898 = tc_term env2 e21  in
                                   (match uu____13898 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____13915 =
                                            let uu____13916 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____13916 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____13915
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
                                          let uu___119_13920 = cres1  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___119_13920.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___119_13920.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___119_13920.FStar_Syntax_Syntax.comp)
                                          }  in
                                        let uu____13921 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____13921 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos
                                                in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____13957 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  let cres3 =
                                                    let uu___120_13962 =
                                                      cres2  in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___120_13962.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___120_13962.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___120_13962.FStar_Syntax_Syntax.comp)
                                                    }  in
                                                  (e, cres3, guard)))))))))
      | uu____13965 -> failwith "Impossible"

and build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
          let uu____13995 =
            let uu____14000 =
              let uu____14001 = FStar_Syntax_Subst.compress t  in
              uu____14001.FStar_Syntax_Syntax.n  in
            let uu____14004 =
              let uu____14005 = FStar_Syntax_Subst.compress lbdef  in
              uu____14005.FStar_Syntax_Syntax.n  in
            (uu____14000, uu____14004)  in
          match uu____13995 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____14011,uu____14012)) ->
              let actuals1 =
                let uu____14050 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp  in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____14050
                  actuals
                 in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1  in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____14071 = FStar_Util.string_of_int n1  in
                       FStar_Util.format1 "%s arguments were found"
                         uu____14071)
                     in
                  let formals_msg =
                    let n1 = FStar_List.length formals  in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____14089 = FStar_Util.string_of_int n1  in
                       FStar_Util.format1 "%s arguments" uu____14089)
                     in
                  let msg =
                    let uu____14097 = FStar_Syntax_Print.term_to_string lbtyp
                       in
                    let uu____14098 =
                      FStar_Syntax_Print.lbname_to_string lbname  in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____14097 uu____14098 formals_msg actuals_msg
                     in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____14105 ->
              let uu____14110 =
                let uu____14111 =
                  let uu____14116 =
                    let uu____14117 = FStar_Syntax_Print.term_to_string lbdef
                       in
                    let uu____14118 = FStar_Syntax_Print.term_to_string lbtyp
                       in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____14117 uu____14118
                     in
                  (uu____14116, (lbtyp.FStar_Syntax_Syntax.pos))  in
                FStar_Errors.Error uu____14111  in
              FStar_Exn.raise uu____14110
           in
        let uu____14119 =
          FStar_List.fold_left
            (fun uu____14145  ->
               fun lb  ->
                 match uu____14145 with
                 | (lbs1,env1) ->
                     let uu____14165 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____14165 with
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
                              (let uu____14185 =
                                 let uu____14192 =
                                   let uu____14193 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____14193
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___121_14204 = env0  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___121_14204.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___121_14204.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___121_14204.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___121_14204.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___121_14204.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___121_14204.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___121_14204.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___121_14204.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___121_14204.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___121_14204.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___121_14204.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___121_14204.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___121_14204.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___121_14204.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___121_14204.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___121_14204.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___121_14204.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___121_14204.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___121_14204.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___121_14204.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___121_14204.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___121_14204.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___121_14204.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___121_14204.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___121_14204.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___121_14204.FStar_TypeChecker_Env.is_native_tactic)
                                    }) t uu____14192
                                  in
                               match uu____14185 with
                               | (t1,uu____14206,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let uu____14210 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____14210);
                                    norm env0 t1))
                             in
                          let env3 =
                            let uu____14212 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2)
                               in
                            if uu____14212
                            then
                              let uu___122_14213 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___122_14213.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___122_14213.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___122_14213.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___122_14213.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___122_14213.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___122_14213.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___122_14213.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___122_14213.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___122_14213.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___122_14213.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___122_14213.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___122_14213.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___122_14213.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___122_14213.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___122_14213.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___122_14213.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___122_14213.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___122_14213.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___122_14213.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___122_14213.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___122_14213.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___122_14213.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___122_14213.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___122_14213.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___122_14213.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___122_14213.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1)
                             in
                          let lb1 =
                            let uu___123_14230 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___123_14230.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___123_14230.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____14119 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____14253 =
        let uu____14262 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____14291 =
                     let uu____14292 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef
                        in
                     uu____14292.FStar_Syntax_Syntax.n  in
                   match uu____14291 with
                   | FStar_Syntax_Syntax.Tm_abs uu____14295 -> ()
                   | uu____14312 ->
                       let uu____14313 =
                         let uu____14314 =
                           let uu____14319 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           ("Only function literals may be defined recursively",
                             uu____14319)
                            in
                         FStar_Errors.Error uu____14314  in
                       FStar_Exn.raise uu____14313);
                  (let uu____14320 =
                     let uu____14327 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp
                        in
                     tc_tot_or_gtot_term uu____14327
                       lb.FStar_Syntax_Syntax.lbdef
                      in
                   match uu____14320 with
                   | (e,c,g) ->
                       ((let uu____14336 =
                           let uu____14337 =
                             FStar_Syntax_Util.is_total_lcomp c  in
                           Prims.op_Negation uu____14337  in
                         if uu____14336
                         then
                           FStar_Exn.raise
                             (FStar_Errors.Error
                                ("Expected let rec to be a Tot term; got effect GTot",
                                  (e.FStar_Syntax_Syntax.pos)))
                         else ());
                        (let lb1 =
                           FStar_Syntax_Util.mk_letbinding
                             lb.FStar_Syntax_Syntax.lbname
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbtyp
                             FStar_Parser_Const.effect_Tot_lid e
                            in
                         (lb1, g))))))
           in
        FStar_All.pipe_right uu____14262 FStar_List.unzip  in
      match uu____14253 with
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t,Prims.bool)
          FStar_Pervasives_Native.tuple5
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____14386 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____14386 with
        | (env1,uu____14404) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____14412 = check_lbtyp top_level env lb  in
            (match uu____14412 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____14456 =
                     tc_maybe_toplevel_term
                       (let uu___124_14465 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___124_14465.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___124_14465.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___124_14465.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___124_14465.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___124_14465.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___124_14465.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___124_14465.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___124_14465.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___124_14465.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___124_14465.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___124_14465.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___124_14465.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___124_14465.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___124_14465.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___124_14465.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___124_14465.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___124_14465.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___124_14465.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___124_14465.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___124_14465.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___124_14465.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___124_14465.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___124_14465.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___124_14465.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___124_14465.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___124_14465.FStar_TypeChecker_Env.is_native_tactic)
                        }) e11
                      in
                   match uu____14456 with
                   | (e12,c1,g1) ->
                       let uu____14479 =
                         let uu____14484 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____14488  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____14484 e12 c1 wf_annot
                          in
                       (match uu____14479 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____14503 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____14503
                              then
                                let uu____14504 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____14505 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____14506 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____14504 uu____14505 uu____14506
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))

and check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_TypeChecker_Env.guard_t,
          FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.subst_elt
                                           Prims.list,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple5
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
             (FStar_Pervasives_Native.None,
               FStar_TypeChecker_Rel.trivial_guard, [], [], env))
        | uu____14550 ->
            let uu____14551 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____14551 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____14600 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____14600)
                 else
                   (let uu____14608 = FStar_Syntax_Util.type_u ()  in
                    match uu____14608 with
                    | (k,uu____14628) ->
                        let uu____14629 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____14629 with
                         | (t2,uu____14651,g) ->
                             ((let uu____14654 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____14654
                               then
                                 let uu____14655 =
                                   let uu____14656 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____14656
                                    in
                                 let uu____14657 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____14655 uu____14657
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____14660 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____14660))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____14668  ->
      match uu____14668 with
      | (x,imp) ->
          let uu____14687 = FStar_Syntax_Util.type_u ()  in
          (match uu____14687 with
           | (tu,u) ->
               ((let uu____14707 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____14707
                 then
                   let uu____14708 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____14709 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____14710 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____14708 uu____14709 uu____14710
                 else ());
                (let uu____14712 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____14712 with
                 | (t,uu____14732,g) ->
                     let x1 =
                       ((let uu___125_14740 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___125_14740.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___125_14740.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____14742 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____14742
                       then
                         let uu____14743 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____14744 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____14743 uu____14744
                       else ());
                      (let uu____14746 = push_binding env x1  in
                       (x1, uu____14746, g, u))))))

and tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun bs  ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> ([], env1, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs2 ->
            let uu____14836 = tc_binder env1 b  in
            (match uu____14836 with
             | (b1,env',g,u) ->
                 let uu____14877 = aux env' bs2  in
                 (match uu____14877 with
                  | (bs3,env'1,g',us) ->
                      let uu____14930 =
                        let uu____14931 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g uu____14931  in
                      ((b1 :: bs3), env'1, uu____14930, (u :: us))))
         in
      aux env bs

and tc_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____15016  ->
             fun uu____15017  ->
               match (uu____15016, uu____15017) with
               | ((t,imp),(args1,g)) ->
                   let uu____15086 = tc_term env1 t  in
                   (match uu____15086 with
                    | (t1,uu____15104,g') ->
                        let uu____15106 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____15106))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____15148  ->
             match uu____15148 with
             | (pats1,g) ->
                 let uu____15173 = tc_args env p  in
                 (match uu____15173 with
                  | (args,g') ->
                      let uu____15186 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____15186))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____15199 = tc_maybe_toplevel_term env e  in
      match uu____15199 with
      | (e1,c,g) ->
          let uu____15215 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____15215
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = c.FStar_Syntax_Syntax.comp ()  in
             let c2 = norm_c env c1  in
             let uu____15228 =
               let uu____15233 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____15233
               then
                 let uu____15238 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____15238, false)
               else
                 (let uu____15240 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____15240, true))
                in
             match uu____15228 with
             | (target_comp,allow_ghost) ->
                 let uu____15249 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____15249 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____15259 =
                        FStar_TypeChecker_Rel.conj_guard g1 g'  in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____15259)
                  | uu____15260 ->
                      if allow_ghost
                      then
                        let uu____15269 =
                          let uu____15270 =
                            let uu____15275 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2
                               in
                            (uu____15275, (e1.FStar_Syntax_Syntax.pos))  in
                          FStar_Errors.Error uu____15270  in
                        FStar_Exn.raise uu____15269
                      else
                        (let uu____15283 =
                           let uu____15284 =
                             let uu____15289 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2
                                in
                             (uu____15289, (e1.FStar_Syntax_Syntax.pos))  in
                           FStar_Errors.Error uu____15284  in
                         FStar_Exn.raise uu____15283)))

and tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
        tc_tot_or_gtot_term env1 e

and tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____15308 = tc_tot_or_gtot_term env t  in
      match uu____15308 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      (let uu____15338 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____15338
       then
         let uu____15339 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____15339
       else ());
      (let env1 =
         let uu___126_15342 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___126_15342.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___126_15342.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___126_15342.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___126_15342.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___126_15342.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___126_15342.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___126_15342.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___126_15342.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___126_15342.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___126_15342.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___126_15342.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___126_15342.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___126_15342.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___126_15342.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___126_15342.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___126_15342.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___126_15342.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___126_15342.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___126_15342.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___126_15342.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___126_15342.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___126_15342.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___126_15342.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___126_15342.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___126_15342.FStar_TypeChecker_Env.is_native_tactic)
         }  in
       let uu____15347 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____15380) ->
             let uu____15381 =
               let uu____15382 =
                 let uu____15387 = FStar_TypeChecker_Env.get_range env1  in
                 ((Prims.strcat "Implicit argument: " msg), uu____15387)  in
               FStar_Errors.Error uu____15382  in
             FStar_Exn.raise uu____15381
          in
       match uu____15347 with
       | (t,c,g) ->
           let uu____15403 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____15403
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____15413 =
                let uu____15414 =
                  let uu____15419 =
                    let uu____15420 = FStar_Syntax_Print.term_to_string e  in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____15420
                     in
                  let uu____15421 = FStar_TypeChecker_Env.get_range env1  in
                  (uu____15419, uu____15421)  in
                FStar_Errors.Error uu____15414  in
              FStar_Exn.raise uu____15413))
  
let level_of_type_fail :
  'Auu____15436 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____15436
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____15449 =
          let uu____15450 =
            let uu____15455 =
              let uu____15456 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Expected a term of type 'Type'; got %s : %s" uu____15456 t
               in
            let uu____15457 = FStar_TypeChecker_Env.get_range env  in
            (uu____15455, uu____15457)  in
          FStar_Errors.Error uu____15450  in
        FStar_Exn.raise uu____15449
  
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____15477 =
            let uu____15478 = FStar_Syntax_Util.unrefine t1  in
            uu____15478.FStar_Syntax_Syntax.n  in
          match uu____15477 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____15482 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____15485 = FStar_Syntax_Util.type_u ()  in
                 match uu____15485 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___129_15493 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___129_15493.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___129_15493.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___129_15493.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___129_15493.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___129_15493.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___129_15493.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___129_15493.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___129_15493.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___129_15493.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___129_15493.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___129_15493.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___129_15493.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___129_15493.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___129_15493.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___129_15493.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___129_15493.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___129_15493.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___129_15493.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___129_15493.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___129_15493.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___129_15493.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___129_15493.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___129_15493.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___129_15493.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___129_15493.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___129_15493.FStar_TypeChecker_Env.is_native_tactic)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____15497 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____15497
                       | uu____15498 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u))
           in
        aux true t
  
let rec universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun e  ->
      let uu____15509 =
        let uu____15510 = FStar_Syntax_Subst.compress e  in
        uu____15510.FStar_Syntax_Syntax.n  in
      match uu____15509 with
      | FStar_Syntax_Syntax.Tm_bvar uu____15515 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____15520 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____15547 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____15563) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____15586,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____15613) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____15620 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____15620 with | ((uu____15631,t),uu____15633) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____15638,(FStar_Util.Inl t,uu____15640),uu____15641) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____15688,(FStar_Util.Inr c,uu____15690),uu____15691) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____15741;
             FStar_Syntax_Syntax.vars = uu____15742;_},us)
          ->
          let uu____15748 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____15748 with
           | ((us',t),uu____15761) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____15767 =
                     let uu____15768 =
                       let uu____15773 = FStar_TypeChecker_Env.get_range env
                          in
                       ("Unexpected number of universe instantiations",
                         uu____15773)
                        in
                     FStar_Errors.Error uu____15768  in
                   FStar_Exn.raise uu____15767)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____15789 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____15790 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____15800) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____15823 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____15823 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____15843  ->
                      match uu____15843 with
                      | (b,uu____15849) ->
                          let uu____15850 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____15850) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____15855 = universe_of_aux env res  in
                 level_of_type env res uu____15855  in
               let u_c =
                 let uu____15857 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____15857 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____15861 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____15861
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2  in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____15954 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____15969 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____16008 ->
                let uu____16009 = universe_of_aux env hd3  in
                (uu____16009, args1)
            | FStar_Syntax_Syntax.Tm_name uu____16022 ->
                let uu____16023 = universe_of_aux env hd3  in
                (uu____16023, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____16036 ->
                let uu____16053 = universe_of_aux env hd3  in
                (uu____16053, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____16066 ->
                let uu____16073 = universe_of_aux env hd3  in
                (uu____16073, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____16086 ->
                let uu____16113 = universe_of_aux env hd3  in
                (uu____16113, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____16126 ->
                let uu____16133 = universe_of_aux env hd3  in
                (uu____16133, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____16146 ->
                let uu____16147 = universe_of_aux env hd3  in
                (uu____16147, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____16160 ->
                let uu____16173 = universe_of_aux env hd3  in
                (uu____16173, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____16186 ->
                let uu____16193 = universe_of_aux env hd3  in
                (uu____16193, args1)
            | FStar_Syntax_Syntax.Tm_type uu____16206 ->
                let uu____16207 = universe_of_aux env hd3  in
                (uu____16207, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____16220,hd4::uu____16222) ->
                let uu____16287 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____16287 with
                 | (uu____16302,uu____16303,hd5) ->
                     let uu____16321 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____16321 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____16372 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____16374 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____16374 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____16425 ->
                let uu____16426 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____16426 with
                 | (env1,uu____16448) ->
                     let env2 =
                       let uu___130_16454 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___130_16454.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___130_16454.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___130_16454.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___130_16454.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___130_16454.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___130_16454.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___130_16454.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___130_16454.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___130_16454.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___130_16454.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___130_16454.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___130_16454.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___130_16454.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___130_16454.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___130_16454.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___130_16454.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___130_16454.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___130_16454.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___130_16454.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___130_16454.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___130_16454.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___130_16454.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___130_16454.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___130_16454.FStar_TypeChecker_Env.is_native_tactic)
                       }  in
                     ((let uu____16456 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____16456
                       then
                         let uu____16457 =
                           let uu____16458 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____16458  in
                         let uu____16459 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____16457 uu____16459
                       else ());
                      (let uu____16461 = tc_term env2 hd3  in
                       match uu____16461 with
                       | (uu____16482,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____16483;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____16485;
                                        FStar_Syntax_Syntax.comp =
                                          uu____16486;_},g)
                           ->
                           ((let uu____16497 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____16497
                               FStar_Pervasives.ignore);
                            (t, args1)))))
             in
          let uu____16508 = type_of_head true hd1 args  in
          (match uu____16508 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____16548 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____16548 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____16592 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____16592)))
      | FStar_Syntax_Syntax.Tm_match (uu____16595,hd1::uu____16597) ->
          let uu____16662 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____16662 with
           | (uu____16665,uu____16666,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____16684,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____16729 = universe_of_aux env e  in
      level_of_type env e uu____16729
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____16750 = tc_binders env tps  in
      match uu____16750 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
  