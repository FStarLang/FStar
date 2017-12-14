open Prims
let instantiate_both : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___284_4 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___284_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___284_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___284_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___284_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___284_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___284_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___284_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___284_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___284_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___284_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___284_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___284_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___284_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___284_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___284_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___284_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___284_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___284_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___284_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___284_4.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___284_4.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___284_4.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___284_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___284_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___284_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___284_4.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___284_4.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___284_4.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___284_4.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___284_4.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___284_4.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___284_4.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___284_4.FStar_TypeChecker_Env.dep_graph)
    }
  
let no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___285_8 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___285_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___285_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___285_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___285_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___285_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___285_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___285_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___285_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___285_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___285_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___285_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___285_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___285_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___285_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___285_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___285_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___285_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___285_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___285_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___285_8.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___285_8.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___285_8.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___285_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___285_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___285_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___285_8.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___285_8.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___285_8.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___285_8.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___285_8.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___285_8.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___285_8.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___285_8.FStar_TypeChecker_Env.dep_graph)
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
           let uu____40 =
             let uu____41 =
               let uu____42 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____43 =
                 let uu____46 = FStar_Syntax_Syntax.as_arg tl1  in [uu____46]
                  in
               uu____42 :: uu____43  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____41
              in
           uu____40 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___279_53  ->
    match uu___279_53 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____56 -> false
  
let steps :
  'Auu____61 . 'Auu____61 -> FStar_TypeChecker_Normalize.step Prims.list =
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
            | uu____107 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____115 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____115 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____125 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____127 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____127
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____129 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____130 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____129 uu____130
                             in
                          let uu____131 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____131
                           in
                        let s =
                          let uu____133 =
                            let uu____134 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____134
                             in
                          FStar_TypeChecker_Util.new_uvar env uu____133  in
                        let uu____143 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s  in
                        match uu____143 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____148 -> fail ()))
             in
          aux false kt
  
let push_binding :
  'Auu____154 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____154) FStar_Pervasives_Native.tuple2 ->
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
        let uu____184 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____184
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
      let uu___286_198 = lc  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___286_198.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags =
          (uu___286_198.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____201  ->
             let uu____202 = lc.FStar_Syntax_Syntax.comp ()  in
             FStar_Syntax_Util.set_result_typ uu____202 t)
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
          let e0 = e  in
          let should_return t =
            let uu____248 =
              let uu____249 = FStar_Syntax_Subst.compress t  in
              uu____249.FStar_Syntax_Syntax.n  in
            match uu____248 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____252,c) ->
                let uu____270 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c)
                   in
                if uu____270
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c)
                     in
                  let uu____272 =
                    let uu____273 = FStar_Syntax_Subst.compress t1  in
                    uu____273.FStar_Syntax_Syntax.n  in
                  (match uu____272 with
                   | FStar_Syntax_Syntax.Tm_constant uu____276 -> false
                   | uu____277 ->
                       let uu____278 = FStar_Syntax_Util.is_unit t1  in
                       Prims.op_Negation uu____278)
                else false
            | uu____280 ->
                let uu____281 = FStar_Syntax_Util.is_unit t  in
                Prims.op_Negation uu____281
             in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____284 =
                  let uu____287 =
                    (let uu____290 = should_return t  in
                     Prims.op_Negation uu____290) ||
                      (let uu____292 =
                         FStar_TypeChecker_Env.should_verify env  in
                       Prims.op_Negation uu____292)
                     in
                  if uu____287
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e  in
                FStar_Syntax_Util.lcomp_of_comp uu____284
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____300 =
            let uu____307 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____307 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____318 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High  in
                  if uu____318
                  then
                    let uu____319 = FStar_Syntax_Print.term_to_string t  in
                    let uu____320 = FStar_Syntax_Print.term_to_string t'  in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____319
                      uu____320
                  else ());
                 (let uu____322 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t'
                     in
                  match uu____322 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                      let uu____338 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____338 with
                       | (e2,g) ->
                           ((let uu____352 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____352
                             then
                               let uu____353 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____354 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____355 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____356 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____353 uu____354 uu____355 uu____356
                             else ());
                            (let msg =
                               let uu____363 =
                                 FStar_TypeChecker_Rel.is_trivial g  in
                               if uu____363
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_40  ->
                                      FStar_Pervasives_Native.Some _0_40)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             let uu____380 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1
                                in
                             match uu____380 with
                             | (lc2,g2) ->
                                 ((memo_tk e2 t'), (set_lcomp_result lc2 t'),
                                   g2))))))
             in
          match uu____300 with
          | (e1,lc1,g) ->
              ((let uu____403 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                if uu____403
                then
                  let uu____404 = FStar_Syntax_Print.lcomp_to_string lc1  in
                  FStar_Util.print1 "Return comp type is %s\n" uu____404
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
        let uu____427 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____427 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____437 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____437 with
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
      fun uu____470  ->
        match uu____470 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____499 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____499
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____501 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____501
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____503 =
              match copt with
              | FStar_Pervasives_Native.Some uu____516 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____519 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____521 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____521))
                     in
                  if uu____519
                  then
                    let uu____528 =
                      let uu____531 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____531  in
                    (uu____528, c)
                  else
                    (let uu____535 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____535
                     then
                       let uu____542 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____542)
                     else
                       (let uu____546 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____546
                        then
                          let uu____553 =
                            let uu____556 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____556  in
                          (uu____553, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____503 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____582 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c
                         in
                      (match uu____582 with
                       | (e1,uu____596,g) ->
                           let g1 =
                             let uu____599 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_TypeChecker_Util.label_guard uu____599
                               "could not prove post-condition" g
                              in
                           ((let uu____601 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low
                                in
                             if uu____601
                             then
                               let uu____602 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____603 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1
                                  in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____602 uu____603
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
  'Auu____610 'Auu____611 .
    FStar_TypeChecker_Env.env ->
      ('Auu____611,'Auu____610,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____611,'Auu____610,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____631  ->
      match uu____631 with
      | (te,kt,f) ->
          let uu____641 = FStar_TypeChecker_Rel.guard_form f  in
          (match uu____641 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____649 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____654 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____649 uu____654)
  
let print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____664 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____664 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____668 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____668
  
let rec get_pat_vars :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats  in
      let uu____692 = FStar_Syntax_Util.head_and_args pats1  in
      match uu____692 with
      | (head1,args) ->
          let uu____731 =
            let uu____732 = FStar_Syntax_Util.un_uinst head1  in
            uu____732.FStar_Syntax_Syntax.n  in
          (match uu____731 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____739 = FStar_List.tl args  in
               get_pat_vars_args uu____739 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____748 ->
               let uu____749 = FStar_Syntax_Free.names pats1  in
               FStar_Util.set_union acc uu____749)

and get_pat_vars_args :
  FStar_Syntax_Syntax.args ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun args  ->
    fun acc  ->
      FStar_List.fold_left
        (fun s  ->
           fun arg  -> get_pat_vars (FStar_Pervasives_Native.fst arg) s) acc
        args

let check_smt_pat :
  'Auu____779 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____779) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____812 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____812
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____813;
                  FStar_Syntax_Syntax.effect_name = uu____814;
                  FStar_Syntax_Syntax.result_typ = uu____815;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____819)::[];
                  FStar_Syntax_Syntax.flags = uu____820;_}
                ->
                let pat_vars =
                  let uu____868 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats
                     in
                  let uu____869 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv  in
                  get_pat_vars uu____868 uu____869  in
                let uu____872 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____899  ->
                          match uu____899 with
                          | (b,uu____905) ->
                              let uu____906 = FStar_Util.set_mem b pat_vars
                                 in
                              Prims.op_Negation uu____906))
                   in
                (match uu____872 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____912) ->
                     let uu____917 =
                       let uu____922 =
                         let uu____923 = FStar_Syntax_Print.bv_to_string x
                            in
                         FStar_Util.format1
                           "Pattern misses at least one bound variable: %s"
                           uu____923
                          in
                       (FStar_Errors.Warning_PatternMissingBoundVar,
                         uu____922)
                        in
                     FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       uu____917)
            | uu____924 -> failwith "Impossible"
          else ()
  
let guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
          FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env  in
            let env1 =
              let uu___287_978 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___287_978.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___287_978.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___287_978.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___287_978.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___287_978.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___287_978.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___287_978.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___287_978.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___287_978.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___287_978.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___287_978.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___287_978.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___287_978.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___287_978.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___287_978.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___287_978.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___287_978.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___287_978.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___287_978.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___287_978.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___287_978.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___287_978.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___287_978.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___287_978.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___287_978.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___287_978.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___287_978.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___287_978.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___287_978.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___287_978.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___287_978.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___287_978.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___287_978.FStar_TypeChecker_Env.dep_graph)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              let filter_types_and_functions bs1 =
                FStar_All.pipe_right bs1
                  (FStar_List.collect
                     (fun uu____1014  ->
                        match uu____1014 with
                        | (b,uu____1022) ->
                            let t =
                              let uu____1024 =
                                FStar_Syntax_Util.unrefine
                                  b.FStar_Syntax_Syntax.sort
                                 in
                              FStar_TypeChecker_Normalize.unfold_whnf env1
                                uu____1024
                               in
                            (match t.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_type uu____1027 -> []
                             | FStar_Syntax_Syntax.Tm_arrow uu____1028 -> []
                             | uu____1041 ->
                                 let uu____1042 =
                                   FStar_Syntax_Syntax.bv_to_name b  in
                                 [uu____1042])))
                 in
              let as_lex_list dec =
                let uu____1047 = FStar_Syntax_Util.head_and_args dec  in
                match uu____1047 with
                | (head1,uu____1063) ->
                    (match head1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.lexcons_lid
                         -> dec
                     | uu____1085 -> mk_lex_list [dec])
                 in
              let cflags = FStar_Syntax_Util.comp_flags c  in
              let uu____1089 =
                FStar_All.pipe_right cflags
                  (FStar_List.tryFind
                     (fun uu___280_1098  ->
                        match uu___280_1098 with
                        | FStar_Syntax_Syntax.DECREASES uu____1099 -> true
                        | uu____1102 -> false))
                 in
              match uu____1089 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                  dec) -> as_lex_list dec
              | uu____1106 ->
                  let xs = FStar_All.pipe_right bs filter_types_and_functions
                     in
                  (match xs with | x::[] -> x | uu____1115 -> mk_lex_list xs)
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____1136 =
              match uu____1136 with
              | (l,t,u_names) ->
                  let uu____1154 =
                    let uu____1155 = FStar_Syntax_Subst.compress t  in
                    uu____1155.FStar_Syntax_Syntax.n  in
                  (match uu____1154 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1216  ->
                                 match uu____1216 with
                                 | (x,imp) ->
                                     let uu____1227 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____1227
                                     then
                                       let uu____1232 =
                                         let uu____1233 =
                                           let uu____1236 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____1236
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1233
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____1232, imp)
                                     else (x, imp)))
                          in
                       let uu____1238 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____1238 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____1257 =
                                let uu____1258 =
                                  let uu____1259 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____1260 =
                                    let uu____1263 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____1263]  in
                                  uu____1259 :: uu____1260  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1258
                                 in
                              uu____1257 FStar_Pervasives_Native.None r  in
                            let uu____1266 = FStar_Util.prefix formals2  in
                            (match uu____1266 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___288_1313 = last1  in
                                   let uu____1314 =
                                     FStar_Syntax_Util.refine last1 precedes1
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___288_1313.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___288_1313.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1314
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____1340 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____1340
                                   then
                                     let uu____1341 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____1342 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____1343 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1341 uu____1342 uu____1343
                                   else ());
                                  (l, t', u_names))))
                   | uu____1347 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos)
               in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
  
let rec tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___289_1790 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___289_1790.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___289_1790.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___289_1790.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___289_1790.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___289_1790.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___289_1790.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___289_1790.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___289_1790.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___289_1790.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___289_1790.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___289_1790.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___289_1790.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___289_1790.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___289_1790.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___289_1790.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___289_1790.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___289_1790.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___289_1790.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___289_1790.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___289_1790.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___289_1790.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___289_1790.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___289_1790.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___289_1790.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___289_1790.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___289_1790.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___289_1790.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___289_1790.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___289_1790.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___289_1790.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___289_1790.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___289_1790.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___289_1790.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____1802 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____1802
       then
         let uu____1803 =
           let uu____1804 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1804  in
         let uu____1805 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____1803 uu____1805
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1814 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1845 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1852 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1869 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1870 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1871 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1872 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1873 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1890 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1903 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1910 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____1911;
              FStar_Syntax_Syntax.vars = uu____1912;_},FStar_Syntax_Syntax.Meta_alien
            (uu____1913,uu____1914,ty))
           ->
           let uu____1924 =
             let uu____1925 = FStar_Syntax_Syntax.mk_Total ty  in
             FStar_All.pipe_right uu____1925 FStar_Syntax_Util.lcomp_of_comp
              in
           (top, uu____1924, FStar_TypeChecker_Rel.trivial_guard)
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1931 = tc_tot_or_gtot_term env1 e1  in
           (match uu____1931 with
            | (e2,c,g) ->
                let g1 =
                  let uu___290_1948 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___290_1948.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___290_1948.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___290_1948.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____1949 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____1949, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1970 = FStar_Syntax_Util.type_u ()  in
           (match uu____1970 with
            | (t,u) ->
                let uu____1983 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____1983 with
                 | (e2,c,g) ->
                     let uu____1999 =
                       let uu____2014 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____2014 with
                       | (env2,uu____2036) -> tc_pats env2 pats  in
                     (match uu____1999 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___291_2070 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___291_2070.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___291_2070.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___291_2070.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____2071 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____2074 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____2071, c, uu____2074))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2082 =
             let uu____2083 = FStar_Syntax_Subst.compress e1  in
             uu____2083.FStar_Syntax_Syntax.n  in
           (match uu____2082 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2092,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2094;
                               FStar_Syntax_Syntax.lbtyp = uu____2095;
                               FStar_Syntax_Syntax.lbeff = uu____2096;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2121 =
                  let uu____2128 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____2128 e11  in
                (match uu____2121 with
                 | (e12,c1,g1) ->
                     let uu____2138 = tc_term env1 e2  in
                     (match uu____2138 with
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
                            let uu____2162 =
                              let uu____2165 =
                                let uu____2166 =
                                  let uu____2179 =
                                    let uu____2186 =
                                      let uu____2189 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13)
                                         in
                                      [uu____2189]  in
                                    (false, uu____2186)  in
                                  (uu____2179, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____2166  in
                              FStar_Syntax_Syntax.mk uu____2165  in
                            uu____2162 FStar_Pervasives_Native.None
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
                          let uu____2211 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e5, c, uu____2211)))
            | uu____2214 ->
                let uu____2215 = tc_term env1 e1  in
                (match uu____2215 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2237) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____2249) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2268 = tc_term env1 e1  in
           (match uu____2268 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2292) ->
           let uu____2339 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____2339 with
            | (env0,uu____2353) ->
                let uu____2358 = tc_comp env0 expected_c  in
                (match uu____2358 with
                 | (expected_c1,uu____2372,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1
                        in
                     let uu____2377 =
                       let uu____2384 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____2384 e1  in
                     (match uu____2377 with
                      | (e2,c',g') ->
                          let uu____2394 =
                            let uu____2401 =
                              let uu____2406 = c'.FStar_Syntax_Syntax.comp ()
                                 in
                              (e2, uu____2406)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2401
                             in
                          (match uu____2394 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inr expected_c2),
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
                                 let uu____2455 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2455
                                  in
                               let topt1 = tc_tactic_opt env0 topt  in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2464 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1
                                             in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2464)
                                  in
                               let uu____2465 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____2465 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2
                                       in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2485) ->
           let uu____2532 = FStar_Syntax_Util.type_u ()  in
           (match uu____2532 with
            | (k,u) ->
                let uu____2545 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____2545 with
                 | (t1,uu____2559,f) ->
                     let uu____2561 =
                       let uu____2568 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____2568 e1  in
                     (match uu____2561 with
                      | (e2,c,g) ->
                          let uu____2578 =
                            let uu____2583 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2587  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2583 e2 c f
                             in
                          (match uu____2578 with
                           | (c1,f1) ->
                               let uu____2596 =
                                 let uu____2603 =
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
                                 comp_check_expected_typ env1 uu____2603 c1
                                  in
                               (match uu____2596 with
                                | (e3,c2,f2) ->
                                    let uu____2643 =
                                      let uu____2644 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2644
                                       in
                                    (e3, c2, uu____2643))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2645;
              FStar_Syntax_Syntax.vars = uu____2646;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____2709 = FStar_Syntax_Util.head_and_args top  in
           (match uu____2709 with
            | (unary_op,uu____2731) ->
                let head1 =
                  let uu____2755 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2755
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
              FStar_Syntax_Syntax.pos = uu____2793;
              FStar_Syntax_Syntax.vars = uu____2794;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____2857 = FStar_Syntax_Util.head_and_args top  in
           (match uu____2857 with
            | (unary_op,uu____2879) ->
                let head1 =
                  let uu____2903 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2903
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
                (FStar_Const.Const_reflect uu____2941);
              FStar_Syntax_Syntax.pos = uu____2942;
              FStar_Syntax_Syntax.vars = uu____2943;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3006 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3006 with
            | (unary_op,uu____3028) ->
                let head1 =
                  let uu____3052 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3052
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
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3090;
              FStar_Syntax_Syntax.vars = uu____3091;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3167 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3167 with
            | (unary_op,uu____3189) ->
                let head1 =
                  let uu____3213 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3213
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
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3257;
              FStar_Syntax_Syntax.vars = uu____3258;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3296 =
             let uu____3303 =
               let uu____3304 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3304  in
             tc_term uu____3303 e1  in
           (match uu____3296 with
            | (e2,c,g) ->
                let uu____3328 = FStar_Syntax_Util.head_and_args top  in
                (match uu____3328 with
                 | (head1,uu____3350) ->
                     let uu____3371 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____3398 =
                       let uu____3399 =
                         let uu____3402 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____3402  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3399
                        in
                     (uu____3371, uu____3398, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3407;
              FStar_Syntax_Syntax.vars = uu____3408;_},(a1,FStar_Pervasives_Native.None
                                                        )::(a2,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3461 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3461 with
            | (head1,uu____3483) ->
                let env' =
                  let uu____3505 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3505  in
                let uu____3506 = tc_term env' a1  in
                (match uu____3506 with
                 | (e1,uu____3520,g1) ->
                     let uu____3522 = tc_term env1 a2  in
                     (match uu____3522 with
                      | (e2,t2,g2) ->
                          let g = FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          let uu____3539 =
                            let uu____3542 =
                              let uu____3543 =
                                let uu____3544 =
                                  FStar_Syntax_Syntax.as_arg a1  in
                                let uu____3545 =
                                  let uu____3548 =
                                    FStar_Syntax_Syntax.as_arg a2  in
                                  [uu____3548]  in
                                uu____3544 :: uu____3545  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3543
                               in
                            uu____3542 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____3539, t2, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3553;
              FStar_Syntax_Syntax.vars = uu____3554;_},uu____3555)
           ->
           let uu____3576 =
             let uu____3581 =
               let uu____3582 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____3582  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3581)  in
           FStar_Errors.raise_error uu____3576 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3589;
              FStar_Syntax_Syntax.vars = uu____3590;_},uu____3591)
           ->
           let uu____3612 =
             let uu____3617 =
               let uu____3618 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____3618  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3617)  in
           FStar_Errors.raise_error uu____3612 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3625;
              FStar_Syntax_Syntax.vars = uu____3626;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____3659 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____3659 with
             | (env0,uu____3673) ->
                 let uu____3678 = tc_term env0 e1  in
                 (match uu____3678 with
                  | (e2,c,g) ->
                      let uu____3694 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____3694 with
                       | (reify_op,uu____3716) ->
                           let u_c =
                             let uu____3738 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                             match uu____3738 with
                             | (uu____3745,c',uu____3747) ->
                                 let uu____3748 =
                                   let uu____3749 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ
                                      in
                                   uu____3749.FStar_Syntax_Syntax.n  in
                                 (match uu____3748 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____3753 ->
                                      let uu____3754 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____3754 with
                                       | (t,u) ->
                                           let g_opt =
                                             FStar_TypeChecker_Rel.try_teq
                                               true env1
                                               c'.FStar_Syntax_Syntax.res_typ
                                               t
                                              in
                                           ((match g_opt with
                                             | FStar_Pervasives_Native.Some
                                                 g' ->
                                                 FStar_TypeChecker_Rel.force_trivial_guard
                                                   env1 g'
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 let uu____3766 =
                                                   let uu____3767 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c'
                                                      in
                                                   let uu____3768 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   let uu____3769 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____3767 uu____3768
                                                     uu____3769
                                                    in
                                                 failwith uu____3766);
                                            u)))
                              in
                           let repr =
                             let uu____3771 = c.FStar_Syntax_Syntax.comp ()
                                in
                             FStar_TypeChecker_Env.reify_comp env1 uu____3771
                               u_c
                              in
                           let e3 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app
                                  (reify_op, [(e2, aqual)]))
                               FStar_Pervasives_Native.None
                               top.FStar_Syntax_Syntax.pos
                              in
                           let c1 =
                             let uu____3792 =
                               FStar_Syntax_Syntax.mk_Total repr  in
                             FStar_All.pipe_right uu____3792
                               FStar_Syntax_Util.lcomp_of_comp
                              in
                           let uu____3793 =
                             comp_check_expected_typ env1 e3 c1  in
                           (match uu____3793 with
                            | (e4,c2,g') ->
                                let uu____3809 =
                                  FStar_TypeChecker_Rel.conj_guard g g'  in
                                (e4, c2, uu____3809))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3811;
              FStar_Syntax_Syntax.vars = uu____3812;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____3854 =
               let uu____3855 =
                 let uu____3860 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____3860)  in
               FStar_Errors.raise_error uu____3855 e1.FStar_Syntax_Syntax.pos
                in
             let uu____3867 = FStar_Syntax_Util.head_and_args top  in
             match uu____3867 with
             | (reflect_op,uu____3889) ->
                 let uu____3910 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____3910 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3943 =
                        let uu____3944 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____3944  in
                      if uu____3943
                      then no_reflect ()
                      else
                        (let uu____3954 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____3954 with
                         | (env_no_ex,topt) ->
                             let uu____3973 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____3993 =
                                   let uu____3996 =
                                     let uu____3997 =
                                       let uu____4012 =
                                         let uu____4015 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____4016 =
                                           let uu____4019 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____4019]  in
                                         uu____4015 :: uu____4016  in
                                       (repr, uu____4012)  in
                                     FStar_Syntax_Syntax.Tm_app uu____3997
                                      in
                                   FStar_Syntax_Syntax.mk uu____3996  in
                                 uu____3993 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____4025 =
                                 let uu____4032 =
                                   let uu____4033 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____4033
                                     FStar_Pervasives_Native.fst
                                    in
                                 tc_tot_or_gtot_term uu____4032 t  in
                               match uu____4025 with
                               | (t1,uu____4061,g) ->
                                   let uu____4063 =
                                     let uu____4064 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____4064.FStar_Syntax_Syntax.n  in
                                   (match uu____4063 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4079,(res,uu____4081)::
                                         (wp,uu____4083)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4126 -> failwith "Impossible")
                                in
                             (match uu____3973 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4157 =
                                    let uu____4162 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____4162 with
                                    | (e2,c,g) ->
                                        ((let uu____4177 =
                                            let uu____4178 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4178
                                             in
                                          if uu____4177
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4192 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____4192 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4200 =
                                                  let uu____4209 =
                                                    let uu____4216 =
                                                      let uu____4217 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____4218 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4217 uu____4218
                                                       in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____4216,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____4209]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4200);
                                               (let uu____4231 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____4231)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4233 =
                                                let uu____4234 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4234
                                                 in
                                              (e2, uu____4233)))
                                     in
                                  (match uu____4157 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4244 =
                                           let uu____4245 =
                                             let uu____4246 =
                                               let uu____4247 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____4247]  in
                                             let uu____4248 =
                                               let uu____4257 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____4257]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4246;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4248;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4245
                                            in
                                         FStar_All.pipe_right uu____4244
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____4277 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____4277 with
                                        | (e4,c1,g') ->
                                            let uu____4293 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____4293))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____4340 =
               let uu____4341 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____4341 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____4340 instantiate_both  in
           ((let uu____4357 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____4357
             then
               let uu____4358 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____4359 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4358
                 uu____4359
             else ());
            (let isquote =
               let uu____4362 = FStar_Syntax_Util.head_and_args head1  in
               match uu____4362 with
               | (head2,uu____4378) ->
                   let uu____4399 =
                     let uu____4400 = FStar_Syntax_Util.un_uinst head2  in
                     uu____4400.FStar_Syntax_Syntax.n  in
                   (match uu____4399 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.quote_lid
                        -> true
                    | uu____4404 -> false)
                in
             let uu____4405 = tc_term (no_inst env2) head1  in
             match uu____4405 with
             | (head2,chead,g_head) ->
                 let uu____4421 =
                   let uu____4428 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____4428
                   then
                     let uu____4435 =
                       let uu____4442 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4442
                        in
                     match uu____4435 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____4455 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____4457 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c
                                    in
                                 Prims.op_Negation uu____4457))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
                              in
                           if uu____4455
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c  in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2  in
                      let uu____4462 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env3 head2 chead g_head args
                        uu____4462)
                    in
                 (match uu____4421 with
                  | (e1,c,g) ->
                      ((let uu____4475 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____4475
                        then
                          let uu____4476 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4476
                        else ());
                       (let uu____4478 = comp_check_expected_typ env0 e1 c
                           in
                        match uu____4478 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4495 =
                                let uu____4496 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____4496.FStar_Syntax_Syntax.n  in
                              match uu____4495 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4500) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___292_4562 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___292_4562.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___292_4562.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___292_4562.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4611 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____4613 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____4613
                               in
                            ((let uu____4615 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____4615
                              then
                                let uu____4616 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____4617 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4616 uu____4617
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4657 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4657 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____4677 = tc_term env12 e1  in
                (match uu____4677 with
                 | (e11,c1,g1) ->
                     let uu____4693 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4703 = FStar_Syntax_Util.type_u ()  in
                           (match uu____4703 with
                            | (k,uu____4713) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k  in
                                let uu____4715 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t
                                   in
                                (uu____4715, res_t))
                        in
                     (match uu____4693 with
                      | (env_branches,res_t) ->
                          ((let uu____4725 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____4725
                            then
                              let uu____4726 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4726
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
                            let uu____4812 =
                              let uu____4817 =
                                FStar_List.fold_right
                                  (fun uu____4863  ->
                                     fun uu____4864  ->
                                       match (uu____4863, uu____4864) with
                                       | ((uu____4927,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4987 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, c) :: caccum), uu____4987))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____4817 with
                              | (cases,g) ->
                                  let uu____5026 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____5026, g)
                               in
                            match uu____4812 with
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
                                           (fun uu____5122  ->
                                              match uu____5122 with
                                              | ((pat,wopt,br),uu____5150,lc,uu____5152)
                                                  ->
                                                  let uu____5165 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ
                                                     in
                                                  (pat, wopt, uu____5165)))
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
                                  let uu____5220 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____5220
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5227 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____5227  in
                                     let lb =
                                       let uu____5231 =
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
                                           uu____5231;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       }  in
                                     let e2 =
                                       let uu____5235 =
                                         let uu____5238 =
                                           let uu____5239 =
                                             let uu____5252 =
                                               let uu____5253 =
                                                 let uu____5254 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____5254]  in
                                               FStar_Syntax_Subst.close
                                                 uu____5253 e_match
                                                in
                                             ((false, [lb]), uu____5252)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5239
                                            in
                                         FStar_Syntax_Syntax.mk uu____5238
                                          in
                                       uu____5235
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____5267 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____5267
                                  then
                                    let uu____5268 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____5269 =
                                      let uu____5270 =
                                        cres.FStar_Syntax_Syntax.comp ()  in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____5270
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5268 uu____5269
                                  else ());
                                 (let uu____5272 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e2, cres, uu____5272))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5275;
                FStar_Syntax_Syntax.lbunivs = uu____5276;
                FStar_Syntax_Syntax.lbtyp = uu____5277;
                FStar_Syntax_Syntax.lbeff = uu____5278;
                FStar_Syntax_Syntax.lbdef = uu____5279;_}::[]),uu____5280)
           ->
           ((let uu____5300 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____5300
             then
               let uu____5301 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____5301
             else ());
            (let uu____5303 = FStar_Options.use_two_phase_tc ()  in
             if uu____5303
             then
               let is_lb_unannotated t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let
                     ((uu____5314,lb::[]),uu____5316) ->
                     let uu____5329 =
                       let uu____5330 =
                         FStar_Syntax_Subst.compress
                           lb.FStar_Syntax_Syntax.lbtyp
                          in
                       uu____5330.FStar_Syntax_Syntax.n  in
                     uu____5329 = FStar_Syntax_Syntax.Tm_unknown
                 | uu____5333 -> failwith "Impossible"  in
               let drop_lbtyp t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let ((t1,lb::[]),t2) ->
                     let uu___293_5353 = t  in
                     let uu____5354 =
                       let uu____5355 =
                         let uu____5368 =
                           let uu____5375 =
                             let uu____5378 =
                               let uu___294_5379 = lb  in
                               let uu____5380 =
                                 FStar_Syntax_Syntax.mk
                                   FStar_Syntax_Syntax.Tm_unknown
                                   FStar_Pervasives_Native.None
                                   (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.pos
                                  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___294_5379.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___294_5379.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = uu____5380;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___294_5379.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___294_5379.FStar_Syntax_Syntax.lbdef)
                               }  in
                             [uu____5378]  in
                           (t1, uu____5375)  in
                         (uu____5368, t2)  in
                       FStar_Syntax_Syntax.Tm_let uu____5355  in
                     {
                       FStar_Syntax_Syntax.n = uu____5354;
                       FStar_Syntax_Syntax.pos =
                         (uu___293_5353.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___293_5353.FStar_Syntax_Syntax.vars)
                     }
                 | uu____5393 -> failwith "Impossible"  in
               let uu____5394 =
                 check_top_level_let
                   (let uu___295_5403 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___295_5403.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___295_5403.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___295_5403.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___295_5403.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___295_5403.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___295_5403.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___295_5403.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___295_5403.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___295_5403.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___295_5403.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___295_5403.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___295_5403.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___295_5403.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___295_5403.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___295_5403.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___295_5403.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___295_5403.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___295_5403.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___295_5403.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___295_5403.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___295_5403.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___295_5403.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___295_5403.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___295_5403.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___295_5403.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___295_5403.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___295_5403.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___295_5403.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___295_5403.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___295_5403.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___295_5403.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___295_5403.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___295_5403.FStar_TypeChecker_Env.dep_graph)
                    }) top
                  in
               match uu____5394 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top
                      in
                   let uu____5414 = FStar_TypeChecker_Env.should_verify env1
                      in
                   (if uu____5414
                    then
                      let uu____5421 =
                        let uu____5422 = is_lb_unannotated top  in
                        if uu____5422 then drop_lbtyp lax_top1 else lax_top1
                         in
                      check_top_level_let env1 uu____5421
                    else (lax_top1, l, g))
             else check_top_level_let env1 top))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5426),uu____5427) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5442;
                FStar_Syntax_Syntax.lbunivs = uu____5443;
                FStar_Syntax_Syntax.lbtyp = uu____5444;
                FStar_Syntax_Syntax.lbeff = uu____5445;
                FStar_Syntax_Syntax.lbdef = uu____5446;_}::uu____5447),uu____5448)
           ->
           ((let uu____5470 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____5470
             then
               let uu____5471 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____5471
             else ());
            (let uu____5473 = FStar_Options.use_two_phase_tc ()  in
             if uu____5473
             then
               let uu____5480 =
                 check_top_level_let_rec
                   (let uu___296_5489 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___296_5489.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___296_5489.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___296_5489.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___296_5489.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___296_5489.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___296_5489.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___296_5489.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___296_5489.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___296_5489.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___296_5489.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___296_5489.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___296_5489.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___296_5489.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___296_5489.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___296_5489.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___296_5489.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___296_5489.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___296_5489.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___296_5489.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___296_5489.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___296_5489.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___296_5489.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___296_5489.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___296_5489.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___296_5489.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___296_5489.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___296_5489.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___296_5489.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___296_5489.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___296_5489.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___296_5489.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___296_5489.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___296_5489.FStar_TypeChecker_Env.dep_graph)
                    }) top
                  in
               match uu____5480 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top
                      in
                   let uu____5500 = FStar_TypeChecker_Env.should_verify env1
                      in
                   (if uu____5500
                    then check_top_level_let_rec env1 lax_top1
                    else (lax_top1, l, g))
             else check_top_level_let_rec env1 top))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5509),uu____5510) ->
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
        let uu____5536 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5626))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5686))::(uu____5687,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5688))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5761 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_SynthByTacticError,
                  "synth_by_tactic: bad application") rng
           in
        match uu____5536 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____5845 = FStar_TypeChecker_Env.expected_typ env  in
                  (match uu____5845 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____5851 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_SynthByTacticError,
                           "synth_by_tactic: need a type annotation when no expected type is present")
                         uu____5851)
               in
            let uu____5854 = FStar_TypeChecker_Env.clear_expected_typ env  in
            (match uu____5854 with
             | (env',uu____5868) ->
                 let uu____5873 = tc_term env' typ  in
                 (match uu____5873 with
                  | (typ1,uu____5887,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____5890 = tc_tactic env' tau  in
                        match uu____5890 with
                        | (tau1,uu____5904,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____5912 =
                                    let uu____5913 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid
                                       in
                                    let uu____5914 =
                                      let uu____5915 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit
                                         in
                                      [uu____5915]  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____5913
                                      uu____5914
                                     in
                                  uu____5912 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth env'
                                       typ1 tau1
                                      in
                                   (let uu____5921 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac")
                                       in
                                    if uu____5921
                                    then
                                      let uu____5922 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      FStar_Util.print1 "Got %s\n" uu____5922
                                    else ());
                                   t)
                                 in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____5925 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng
                                  in
                               tc_term env uu____5925)))))))

and tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___297_5929 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___297_5929.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___297_5929.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___297_5929.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___297_5929.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___297_5929.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___297_5929.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___297_5929.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___297_5929.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___297_5929.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___297_5929.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___297_5929.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___297_5929.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___297_5929.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___297_5929.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___297_5929.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___297_5929.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___297_5929.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___297_5929.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___297_5929.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___297_5929.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___297_5929.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___297_5929.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___297_5929.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___297_5929.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___297_5929.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___297_5929.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___297_5929.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___297_5929.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___297_5929.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___297_5929.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___297_5929.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___297_5929.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___297_5929.FStar_TypeChecker_Env.dep_graph)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit

and tc_reified_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___298_5933 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___298_5933.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___298_5933.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___298_5933.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___298_5933.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___298_5933.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___298_5933.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___298_5933.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___298_5933.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___298_5933.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___298_5933.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___298_5933.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___298_5933.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___298_5933.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___298_5933.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___298_5933.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___298_5933.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___298_5933.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___298_5933.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___298_5933.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___298_5933.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___298_5933.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___298_5933.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___298_5933.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___298_5933.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___298_5933.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___298_5933.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___298_5933.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___298_5933.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___298_5933.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___298_5933.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___298_5933.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___298_5933.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___298_5933.FStar_TypeChecker_Env.dep_graph)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit

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
          let uu____5949 = tc_tactic env tactic  in
          (match uu____5949 with
           | (tactic1,uu____5959,uu____5960) ->
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
        let uu____5999 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____5999 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____6020 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____6020
              then FStar_Util.Inl t1
              else
                (let uu____6026 =
                   let uu____6027 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6027
                    in
                 FStar_Util.Inr uu____6026)
               in
            let is_data_ctor uu___281_6037 =
              match uu___281_6037 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6040) -> true
              | uu____6047 -> false  in
            let uu____6050 =
              (is_data_ctor dc) &&
                (let uu____6052 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____6052)
               in
            if uu____6050
            then
              let uu____6059 =
                let uu____6064 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____6064)  in
              let uu____6065 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____6059 uu____6065
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6082 =
            let uu____6083 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6083
             in
          failwith uu____6082
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6117 =
              let uu____6118 = FStar_Syntax_Subst.compress t1  in
              uu____6118.FStar_Syntax_Syntax.n  in
            match uu____6117 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6121 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6134 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___299_6172 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___299_6172.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___299_6172.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___299_6172.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____6224 =
            let uu____6237 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____6237 with
            | FStar_Pervasives_Native.None  ->
                let uu____6252 = FStar_Syntax_Util.type_u ()  in
                (match uu____6252 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard)
             in
          (match uu____6224 with
           | (t,uu____6289,g0) ->
               let uu____6303 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____6303 with
                | (e1,uu____6323,g1) ->
                    let uu____6337 =
                      let uu____6338 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____6338
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____6339 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____6337, uu____6339)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6341 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6354 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____6354)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____6341 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___300_6373 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___300_6373.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___300_6373.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____6376 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____6376 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6397 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____6397
                       then FStar_Util.Inl t1
                       else
                         (let uu____6403 =
                            let uu____6404 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6404
                             in
                          FStar_Util.Inr uu____6403)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6410;
             FStar_Syntax_Syntax.vars = uu____6411;_},uu____6412)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6417 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6417
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6425 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6425
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6433;
             FStar_Syntax_Syntax.vars = uu____6434;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____6443 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6443 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6466 =
                     let uu____6471 =
                       let uu____6472 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____6473 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____6474 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____6472 uu____6473 uu____6474
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____6471)
                      in
                   let uu____6475 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____6466 uu____6475)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6491 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6495 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6495 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6497 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6497 with
           | ((us,t),range) ->
               ((let uu____6520 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____6520
                 then
                   let uu____6521 =
                     let uu____6522 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____6522  in
                   let uu____6523 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6524 = FStar_Range.string_of_range range  in
                   let uu____6525 = FStar_Range.string_of_use_range range  in
                   let uu____6526 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6521 uu____6523 uu____6524 uu____6525 uu____6526
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6531 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6531 us  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6555 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6555 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____6569 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6569 with
                | (env2,uu____6583) ->
                    let uu____6588 = tc_binders env2 bs1  in
                    (match uu____6588 with
                     | (bs2,env3,g,us) ->
                         let uu____6607 = tc_comp env3 c1  in
                         (match uu____6607 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___301_6626 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___301_6626.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___301_6626.FStar_Syntax_Syntax.vars)
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
                                  let uu____6635 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6635
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
          let uu____6654 =
            let uu____6659 =
              let uu____6660 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____6660]  in
            FStar_Syntax_Subst.open_term uu____6659 phi  in
          (match uu____6654 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____6670 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6670 with
                | (env2,uu____6684) ->
                    let uu____6689 =
                      let uu____6702 = FStar_List.hd x1  in
                      tc_binder env2 uu____6702  in
                    (match uu____6689 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6730 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____6730
                           then
                             let uu____6731 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6732 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____6733 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6731 uu____6732 uu____6733
                           else ());
                          (let uu____6735 = FStar_Syntax_Util.type_u ()  in
                           match uu____6735 with
                           | (t_phi,uu____6747) ->
                               let uu____6748 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____6748 with
                                | (phi2,uu____6762,f2) ->
                                    let e1 =
                                      let uu___302_6767 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___302_6767.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___302_6767.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____6774 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6774
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6787) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____6810 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____6810
            then
              let uu____6811 =
                FStar_Syntax_Print.term_to_string
                  (let uu___303_6814 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___303_6814.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___303_6814.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6811
            else ());
           (let uu____6820 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____6820 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____6833 ->
          let uu____6834 =
            let uu____6835 = FStar_Syntax_Print.term_to_string top  in
            let uu____6836 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____6835
              uu____6836
             in
          failwith uu____6834

and tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____6846 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____6847,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____6858,FStar_Pervasives_Native.Some msize) ->
            FStar_Syntax_Syntax.tconst
              (match msize with
               | (FStar_Const.Signed ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.int8_lid
               | (FStar_Const.Signed ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.int16_lid
               | (FStar_Const.Signed ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.int32_lid
               | (FStar_Const.Signed ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.int64_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.uint8_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.uint16_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.uint32_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.uint64_lid)
        | FStar_Const.Const_string uu____6874 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____6879 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____6880 ->
            let uu____6881 =
              let uu____6886 =
                FStar_ToSyntax_Env.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____6886 FStar_Util.must  in
            FStar_All.pipe_right uu____6881 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____6911 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____6912 =
              let uu____6917 =
                let uu____6918 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6918
                 in
              (FStar_Errors.Fatal_IllTyped, uu____6917)  in
            FStar_Errors.raise_error uu____6912 r
        | FStar_Const.Const_set_range_of  ->
            let uu____6919 =
              let uu____6924 =
                let uu____6925 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6925
                 in
              (FStar_Errors.Fatal_IllTyped, uu____6924)  in
            FStar_Errors.raise_error uu____6919 r
        | FStar_Const.Const_reify  ->
            let uu____6926 =
              let uu____6931 =
                let uu____6932 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6932
                 in
              (FStar_Errors.Fatal_IllTyped, uu____6931)  in
            FStar_Errors.raise_error uu____6926 r
        | FStar_Const.Const_reflect uu____6933 ->
            let uu____6934 =
              let uu____6939 =
                let uu____6940 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6940
                 in
              (FStar_Errors.Fatal_IllTyped, uu____6939)  in
            FStar_Errors.raise_error uu____6934 r
        | uu____6941 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r

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
      | FStar_Syntax_Syntax.Total (t,uu____6958) ->
          let uu____6967 = FStar_Syntax_Util.type_u ()  in
          (match uu____6967 with
           | (k,u) ->
               let uu____6980 = tc_check_tot_or_gtot_term env t k  in
               (match uu____6980 with
                | (t1,uu____6994,g) ->
                    let uu____6996 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____6996, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____6998) ->
          let uu____7007 = FStar_Syntax_Util.type_u ()  in
          (match uu____7007 with
           | (k,u) ->
               let uu____7020 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7020 with
                | (t1,uu____7034,g) ->
                    let uu____7036 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7036, u, g)))
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
            let uu____7044 =
              let uu____7045 =
                let uu____7046 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____7046 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7045  in
            uu____7044 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____7049 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____7049 with
           | (tc1,uu____7063,f) ->
               let uu____7065 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____7065 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7109 =
                        let uu____7110 = FStar_Syntax_Subst.compress head3
                           in
                        uu____7110.FStar_Syntax_Syntax.n  in
                      match uu____7109 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7113,us) -> us
                      | uu____7119 -> []  in
                    let uu____7120 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____7120 with
                     | (uu____7141,args1) ->
                         let uu____7163 =
                           let uu____7182 = FStar_List.hd args1  in
                           let uu____7195 = FStar_List.tl args1  in
                           (uu____7182, uu____7195)  in
                         (match uu____7163 with
                          | (res,args2) ->
                              let uu____7260 =
                                let uu____7269 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___282_7297  ->
                                          match uu___282_7297 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7305 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____7305 with
                                               | (env1,uu____7317) ->
                                                   let uu____7322 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____7322 with
                                                    | (e1,uu____7334,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____7269
                                  FStar_List.unzip
                                 in
                              (match uu____7260 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___304_7373 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___304_7373.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___304_7373.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____7377 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____7377 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____7381 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____7381))))))

and tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7389 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7390 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7400 = aux u3  in FStar_Syntax_Syntax.U_succ uu____7400
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7404 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____7404
        | FStar_Syntax_Syntax.U_name x -> u2  in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7409 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____7409 FStar_Pervasives_Native.snd
         | uu____7418 -> aux u)

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
            let uu____7442 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____7442 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7536 bs2 bs_expected1 =
              match uu____7536 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7704)) ->
                             let uu____7709 =
                               let uu____7714 =
                                 let uu____7715 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7715
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7714)
                                in
                             let uu____7716 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____7709 uu____7716
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7717),FStar_Pervasives_Native.None ) ->
                             let uu____7722 =
                               let uu____7727 =
                                 let uu____7728 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7728
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7727)
                                in
                             let uu____7729 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____7722 uu____7729
                         | uu____7730 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____7736 =
                           let uu____7741 =
                             let uu____7742 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____7742.FStar_Syntax_Syntax.n  in
                           match uu____7741 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7749 ->
                               ((let uu____7751 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____7751
                                 then
                                   let uu____7752 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7752
                                 else ());
                                (let uu____7754 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____7754 with
                                 | (t,uu____7766,g1) ->
                                     let g2 =
                                       let uu____7769 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       if uu____7769
                                       then
                                         FStar_TypeChecker_Rel.trivial_guard
                                       else
                                         (let uu____7771 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____7771 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____7774 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____7779 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____7774 uu____7779
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____7781 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____7781
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2)
                                        in
                                     let g3 =
                                       let uu____7783 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7783
                                        in
                                     (t, g3)))
                            in
                         match uu____7736 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___305_7811 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___305_7811.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___305_7811.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____7824 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____7824
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
                  | uu____7972 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____7981 = tc_binders env1 bs  in
                  match uu____7981 with
                  | (bs1,envbody,g,uu____8011) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____8055 =
                    let uu____8056 = FStar_Syntax_Subst.compress t2  in
                    uu____8056.FStar_Syntax_Syntax.n  in
                  match uu____8055 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8079 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8103 -> failwith "Impossible");
                       (let uu____8112 = tc_binders env1 bs  in
                        match uu____8112 with
                        | (bs1,envbody,g,uu____8144) ->
                            let uu____8145 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____8145 with
                             | (envbody1,uu____8173) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8184;
                         FStar_Syntax_Syntax.pos = uu____8185;
                         FStar_Syntax_Syntax.vars = uu____8186;_},uu____8187)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8231 -> failwith "Impossible");
                       (let uu____8240 = tc_binders env1 bs  in
                        match uu____8240 with
                        | (bs1,envbody,g,uu____8272) ->
                            let uu____8273 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____8273 with
                             | (envbody1,uu____8301) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8313) ->
                      let uu____8318 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____8318 with
                       | (uu____8359,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8402 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____8402 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____8511 c_expected2 body3
                               =
                               match uu____8511 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8631 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____8631, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8662 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8662
                                           in
                                        let uu____8663 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____8663, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____8688 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____8688
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
                                               let uu____8740 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____8740 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8763 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____8763 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____8813 =
                                                           let uu____8844 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____8844,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____8813
                                                           c_expected4 body3))
                                           | uu____8861 ->
                                               let body4 =
                                                 FStar_Syntax_Util.abs
                                                   more_bs body3
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env3, bs2, guard, c, body4))
                                        else
                                          (let body4 =
                                             FStar_Syntax_Util.abs more_bs
                                               body3
                                               FStar_Pervasives_Native.None
                                              in
                                           (env3, bs2, guard, c, body4)))
                                in
                             let uu____8877 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____8877 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___306_8938 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___306_8938.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___306_8938.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___306_8938.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___306_8938.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___306_8938.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___306_8938.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___306_8938.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___306_8938.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___306_8938.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___306_8938.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___306_8938.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___306_8938.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___306_8938.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___306_8938.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___306_8938.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___306_8938.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___306_8938.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___306_8938.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___306_8938.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___306_8938.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___306_8938.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___306_8938.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___306_8938.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___306_8938.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___306_8938.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___306_8938.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___306_8938.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___306_8938.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___306_8938.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___306_8938.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___306_8938.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___306_8938.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___306_8938.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____8986  ->
                                     fun uu____8987  ->
                                       match (uu____8986, uu____8987) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____9049 =
                                             let uu____9056 =
                                               let uu____9057 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9057
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____9056 t3  in
                                           (match uu____9049 with
                                            | (t4,uu____9079,uu____9080) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9090 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___307_9093
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___307_9093.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___307_9093.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____9090 ::
                                                        letrec_binders
                                                  | uu____9094 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____9099 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____9099 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____9153 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____9153 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, g))))
                  | uu____9199 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9220 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____9220
                      else
                        (let uu____9222 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____9222 with
                         | (uu____9261,bs1,uu____9263,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____9283 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____9283 with
          | (env1,topt) ->
              ((let uu____9303 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____9303
                then
                  let uu____9304 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9304
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9308 = expected_function_typ1 env1 topt body  in
                match uu____9308 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9348 =
                      let should_check_expected_effect =
                        let uu____9356 =
                          let uu____9363 =
                            let uu____9364 =
                              FStar_Syntax_Subst.compress body1  in
                            uu____9364.FStar_Syntax_Syntax.n  in
                          (c_opt, uu____9363)  in
                        match uu____9356 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9369,(FStar_Util.Inr expected_c,uu____9371),uu____9372))
                            -> false
                        | uu____9421 -> true  in
                      let uu____9428 =
                        tc_term
                          (let uu___308_9437 = envbody  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___308_9437.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___308_9437.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___308_9437.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___308_9437.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___308_9437.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___308_9437.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___308_9437.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___308_9437.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___308_9437.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___308_9437.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___308_9437.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___308_9437.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___308_9437.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___308_9437.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___308_9437.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___308_9437.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___308_9437.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___308_9437.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___308_9437.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___308_9437.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___308_9437.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___308_9437.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___308_9437.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___308_9437.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___308_9437.FStar_TypeChecker_Env.qname_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___308_9437.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth =
                               (uu___308_9437.FStar_TypeChecker_Env.synth);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___308_9437.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___308_9437.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___308_9437.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___308_9437.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___308_9437.FStar_TypeChecker_Env.dep_graph)
                           }) body1
                         in
                      match uu____9428 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body
                             in
                          if should_check_expected_effect
                          then
                            let uu____9454 =
                              let uu____9461 =
                                let uu____9466 =
                                  cbody.FStar_Syntax_Syntax.comp ()  in
                                (body2, uu____9466)  in
                              check_expected_effect
                                (let uu___309_9473 = envbody  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___309_9473.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___309_9473.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___309_9473.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___309_9473.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___309_9473.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___309_9473.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___309_9473.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___309_9473.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___309_9473.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___309_9473.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___309_9473.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___309_9473.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___309_9473.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___309_9473.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___309_9473.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___309_9473.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___309_9473.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___309_9473.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___309_9473.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___309_9473.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___309_9473.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___309_9473.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___309_9473.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___309_9473.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___309_9473.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___309_9473.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___309_9473.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___309_9473.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___309_9473.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___309_9473.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___309_9473.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___309_9473.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___309_9473.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9461
                               in
                            (match uu____9454 with
                             | (body3,cbody1,guard) ->
                                 let uu____9483 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard
                                    in
                                 (body3, cbody1, uu____9483))
                          else
                            (let uu____9485 =
                               cbody.FStar_Syntax_Syntax.comp ()  in
                             (body2, uu____9485, guard_body1))
                       in
                    (match uu____9348 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9500 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9502 =
                                  FStar_TypeChecker_Env.should_verify env1
                                   in
                                Prims.op_Negation uu____9502)
                              in
                           if uu____9500
                           then
                             let uu____9503 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9503
                           else
                             (let guard1 =
                                let uu____9506 =
                                  FStar_TypeChecker_Rel.conj_guard g guard
                                   in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9506
                                 in
                              guard1)
                            in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody  in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt)))
                            in
                         let uu____9515 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t  in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9536 ->
                                    (e, t1, guard1)
                                | uu____9549 ->
                                    let uu____9550 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1
                                       in
                                    (match uu____9550 with
                                     | (e1,guard') ->
                                         let uu____9563 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard'
                                            in
                                         (e1, t1, uu____9563)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1)
                            in
                         (match uu____9515 with
                          | (e1,tfun,guard2) ->
                              let c =
                                if env1.FStar_TypeChecker_Env.top_level
                                then FStar_Syntax_Syntax.mk_Total tfun
                                else
                                  FStar_TypeChecker_Util.return_value env1
                                    tfun e1
                                 in
                              let uu____9577 =
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  (FStar_Syntax_Util.lcomp_of_comp c) guard2
                                 in
                              (match uu____9577 with
                               | (c1,g1) -> (e1, c1, g1))))))

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
              (let uu____9626 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____9626
               then
                 let uu____9627 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____9628 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9627
                   uu____9628
               else ());
              (let monadic_application uu____9685 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9685 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres1 =
                       let uu___310_9744 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___310_9744.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___310_9744.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___310_9744.FStar_Syntax_Syntax.comp)
                       }  in
                     let uu____9745 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1
                              in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard
                              in
                           (cres2, g)
                       | uu____9760 ->
                           let g =
                             let uu____9768 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard
                                in
                             FStar_All.pipe_right uu____9768
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____9769 =
                             let uu____9770 =
                               let uu____9773 =
                                 let uu____9774 =
                                   let uu____9775 =
                                     cres1.FStar_Syntax_Syntax.comp ()  in
                                   FStar_Syntax_Util.arrow bs uu____9775  in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____9774
                                  in
                               FStar_Syntax_Syntax.mk_Total uu____9773  in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9770
                              in
                           (uu____9769, g)
                        in
                     (match uu____9745 with
                      | (cres2,guard1) ->
                          ((let uu____9789 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____9789
                            then
                              let uu____9790 =
                                FStar_Syntax_Print.lcomp_to_string cres2  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____9790
                            else ());
                           (let cres3 =
                              let uu____9793 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2
                                 in
                              if uu____9793
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
                                   fun uu____9827  ->
                                     match uu____9827 with
                                     | ((e,q),x,c) ->
                                         let uu____9860 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____9860
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
                              let uu____9872 =
                                let uu____9873 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____9873.FStar_Syntax_Syntax.n  in
                              match uu____9872 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____9877 -> false  in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____9898  ->
                                         match uu____9898 with
                                         | (arg,uu____9912,uu____9913) -> arg
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
                                (let uu____9923 =
                                   let map_fun uu____9985 =
                                     match uu____9985 with
                                     | ((e,q),uu____10020,c) ->
                                         let uu____10030 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____10030
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
                                            let uu____10080 =
                                              let uu____10085 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              (uu____10085, q)  in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____10080))
                                      in
                                   let uu____10114 =
                                     let uu____10139 =
                                       let uu____10162 =
                                         let uu____10177 =
                                           let uu____10186 =
                                             FStar_Syntax_Syntax.as_arg head2
                                              in
                                           (uu____10186,
                                             FStar_Pervasives_Native.None,
                                             chead1)
                                            in
                                         uu____10177 :: arg_comps_rev  in
                                       FStar_List.map map_fun uu____10162  in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10139
                                      in
                                   match uu____10114 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10359 =
                                         let uu____10360 =
                                           FStar_List.hd reverse_args  in
                                         FStar_Pervasives_Native.fst
                                           uu____10360
                                          in
                                       let uu____10369 =
                                         let uu____10376 =
                                           FStar_List.tl reverse_args  in
                                         FStar_List.rev uu____10376  in
                                       (lifted_args, uu____10359,
                                         uu____10369)
                                    in
                                 match uu____9923 with
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
                                     let bind_lifted_args e uu___283_10479 =
                                       match uu___283_10479 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1
                                              in
                                           let letbinding =
                                             let uu____10534 =
                                               let uu____10537 =
                                                 let uu____10538 =
                                                   let uu____10551 =
                                                     let uu____10552 =
                                                       let uu____10553 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____10553]  in
                                                     FStar_Syntax_Subst.close
                                                       uu____10552 e
                                                      in
                                                   ((false, [lb]),
                                                     uu____10551)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10538
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10537
                                                in
                                             uu____10534
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
                            let uu____10583 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1
                               in
                            match uu____10583 with
                            | (comp2,g) -> (app, comp2, g))))
                  in
               let rec tc_args head_info uu____10674 bs args1 =
                 match uu____10674 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____10821))::rest,
                         (uu____10823,FStar_Pervasives_Native.None )::uu____10824)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          let uu____10885 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____10885 with
                           | (varg,uu____10905,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1
                                  in
                               let arg =
                                 let uu____10927 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____10927)  in
                               let uu____10928 =
                                 let uu____10963 =
                                   let uu____10978 =
                                     let uu____10991 =
                                       let uu____10992 =
                                         FStar_Syntax_Syntax.mk_Total t1  in
                                       FStar_All.pipe_right uu____10992
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____10991)
                                      in
                                   uu____10978 :: outargs  in
                                 let uu____11011 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst2, uu____10963, (arg :: arg_rets),
                                   uu____11011, fvs)
                                  in
                               tc_args head_info uu____10928 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11113),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11114)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11127 ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier")
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___311_11138 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___311_11138.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___311_11138.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____11140 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____11140
                             then
                               let uu____11141 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11141
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
                               let uu___312_11146 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___312_11146.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___312_11146.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___312_11146.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___312_11146.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___312_11146.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___312_11146.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___312_11146.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___312_11146.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___312_11146.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___312_11146.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___312_11146.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___312_11146.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___312_11146.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___312_11146.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___312_11146.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___312_11146.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___312_11146.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___312_11146.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___312_11146.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___312_11146.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___312_11146.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___312_11146.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___312_11146.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___312_11146.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___312_11146.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___312_11146.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___312_11146.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___312_11146.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___312_11146.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___312_11146.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___312_11146.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___312_11146.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___312_11146.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             (let uu____11148 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High
                                 in
                              if uu____11148
                              then
                                let uu____11149 =
                                  FStar_Syntax_Print.tag_of_term e  in
                                let uu____11150 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11151 =
                                  FStar_Syntax_Print.term_to_string targ1  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11149 uu____11150 uu____11151
                              else ());
                             (let uu____11153 = tc_term env2 e  in
                              match uu____11153 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e1, aq)  in
                                  let xterm =
                                    let uu____11188 =
                                      let uu____11191 =
                                        let uu____11198 =
                                          FStar_Syntax_Syntax.bv_to_name x1
                                           in
                                        FStar_Syntax_Syntax.as_arg
                                          uu____11198
                                         in
                                      FStar_Pervasives_Native.fst uu____11191
                                       in
                                    (uu____11188, aq)  in
                                  let uu____11205 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name)
                                     in
                                  if uu____11205
                                  then
                                    let subst2 =
                                      let uu____11213 = FStar_List.hd bs  in
                                      maybe_extend_subst subst1 uu____11213
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
                      | (uu____11339,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11375) ->
                          let uu____11426 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____11426 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11460 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____11460
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11485 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____11485 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1))
                                             in
                                          ((let uu____11508 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____11508
                                            then
                                              FStar_Errors.log_issue
                                                tres1.FStar_Syntax_Syntax.pos
                                                (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                  "Potentially redundant explicit currying of a function type")
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____11550 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____11556 =
                                         let uu____11557 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____11557.FStar_Syntax_Syntax.n
                                          in
                                       match uu____11556 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____11560;
                                              FStar_Syntax_Syntax.index =
                                                uu____11561;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____11563)
                                           -> norm_tres tres4
                                       | uu____11570 -> tres3  in
                                     let uu____11571 = norm_tres tres1  in
                                     aux true uu____11571
                                 | uu____11572 ->
                                     let uu____11573 =
                                       let uu____11578 =
                                         let uu____11579 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____11580 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         FStar_Util.format2
                                           "Too many arguments to function of type %s; got %s arguments"
                                           uu____11579 uu____11580
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____11578)
                                        in
                                     let uu____11587 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____11573
                                       uu____11587
                                  in
                               aux false chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf =
                 let uu____11606 =
                   let uu____11607 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____11607.FStar_Syntax_Syntax.n  in
                 match uu____11606 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11618 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11719 = tc_term env1 e  in
                           (match uu____11719 with
                            | (e1,c,g_e) ->
                                let uu____11741 = tc_args1 env1 tl1  in
                                (match uu____11741 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11781 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11781)))
                        in
                     let uu____11802 = tc_args1 env args  in
                     (match uu____11802 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11839 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11877  ->
                                      match uu____11877 with
                                      | (uu____11890,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____11839
                             in
                          let ml_or_tot t r1 =
                            let uu____11907 = FStar_Options.ml_ish ()  in
                            if uu____11907
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____11910 =
                              let uu____11913 =
                                let uu____11914 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____11914
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_uvar env uu____11913
                               in
                            ml_or_tot uu____11910 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____11927 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____11927
                            then
                              let uu____11928 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____11929 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____11930 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11928 uu____11929 uu____11930
                            else ());
                           (let uu____11933 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11933);
                           (let comp =
                              let uu____11935 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____11946  ->
                                   fun out  ->
                                     match uu____11946 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11935
                               in
                            let uu____11960 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r
                               in
                            let uu____11963 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____11960, comp, uu____11963))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11966;
                        FStar_Syntax_Syntax.pos = uu____11967;
                        FStar_Syntax_Syntax.vars = uu____11968;_},uu____11969)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____12090 = tc_term env1 e  in
                           (match uu____12090 with
                            | (e1,c,g_e) ->
                                let uu____12112 = tc_args1 env1 tl1  in
                                (match uu____12112 with
                                 | (args2,comps,g_rest) ->
                                     let uu____12152 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____12152)))
                        in
                     let uu____12173 = tc_args1 env args  in
                     (match uu____12173 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12210 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12248  ->
                                      match uu____12248 with
                                      | (uu____12261,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____12210
                             in
                          let ml_or_tot t r1 =
                            let uu____12278 = FStar_Options.ml_ish ()  in
                            if uu____12278
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____12281 =
                              let uu____12284 =
                                let uu____12285 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____12285
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_uvar env uu____12284
                               in
                            ml_or_tot uu____12281 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____12298 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____12298
                            then
                              let uu____12299 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____12300 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____12301 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12299 uu____12300 uu____12301
                            else ());
                           (let uu____12304 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12304);
                           (let comp =
                              let uu____12306 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____12317  ->
                                   fun out  ->
                                     match uu____12317 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12306
                               in
                            let uu____12331 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r
                               in
                            let uu____12334 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____12331, comp, uu____12334))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12355 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____12355 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1))
                             in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12420) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12426,uu____12427) -> check_function_app t
                 | uu____12468 ->
                     let uu____12469 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____12469
                       head1.FStar_Syntax_Syntax.pos
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
                  let uu____12543 =
                    FStar_List.fold_left2
                      (fun uu____12586  ->
                         fun uu____12587  ->
                           fun uu____12588  ->
                             match (uu____12586, uu____12587, uu____12588)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                        "Inconsistent implicit qualifiers")
                                      e.FStar_Syntax_Syntax.pos
                                  else ();
                                  (let uu____12656 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____12656 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____12674 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12674 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12678 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____12678)
                                              &&
                                              (let uu____12680 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____12680))
                                          in
                                       let uu____12681 =
                                         let uu____12690 =
                                           let uu____12699 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____12699]  in
                                         FStar_List.append seen uu____12690
                                          in
                                       let uu____12706 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____12681, uu____12706, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____12543 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____12742 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____12742
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____12744 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____12744 with | (c2,g) -> (e, c2, g)))
              | uu____12761 ->
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
        let uu____12795 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____12795 with
        | (pattern,when_clause,branch_exp) ->
            let uu____12831 = branch1  in
            (match uu____12831 with
             | (cpat,uu____12863,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____12930 = FStar_Syntax_Util.type_u ()  in
                     match uu____12930 with
                     | (tu,u) ->
                         let uu____12941 =
                           tc_check_tot_or_gtot_term env1 t tu  in
                         (match uu____12941 with
                          | (t1,uu____12953,g) -> (t1, g))
                      in
                   let uu____12955 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot
                      in
                   match uu____12955 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____12989 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____12989
                         then
                           let uu____12990 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____12991 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12990 uu____12991
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____12994 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____12994 with
                         | (env1,uu____13016) ->
                             let env11 =
                               let uu___313_13022 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___313_13022.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___313_13022.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___313_13022.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___313_13022.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___313_13022.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___313_13022.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___313_13022.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___313_13022.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___313_13022.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___313_13022.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___313_13022.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___313_13022.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___313_13022.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___313_13022.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___313_13022.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___313_13022.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___313_13022.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___313_13022.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___313_13022.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___313_13022.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___313_13022.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___313_13022.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___313_13022.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___313_13022.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___313_13022.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___313_13022.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___313_13022.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___313_13022.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___313_13022.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___313_13022.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___313_13022.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___313_13022.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___313_13022.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             ((let uu____13025 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High
                                  in
                               if uu____13025
                               then
                                 let uu____13026 =
                                   FStar_Syntax_Print.term_to_string exp  in
                                 let uu____13027 =
                                   FStar_Syntax_Print.term_to_string pat_t
                                    in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____13026 uu____13027
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t
                                  in
                               let uu____13030 =
                                 tc_tot_or_gtot_term env12 exp  in
                               match uu____13030 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___314_13055 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___314_13055.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___314_13055.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___314_13055.FStar_TypeChecker_Env.implicits)
                                     }  in
                                   let uu____13056 =
                                     let uu____13057 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t
                                        in
                                     if uu____13057
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13059 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1
                                          in
                                       FStar_All.pipe_right uu____13059
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____13061 =
                                          let uu____13066 =
                                            let uu____13067 =
                                              FStar_Syntax_Print.term_to_string
                                                lc.FStar_Syntax_Syntax.res_typ
                                               in
                                            let uu____13068 =
                                              FStar_Syntax_Print.term_to_string
                                                expected_pat_t
                                               in
                                            FStar_Util.format2
                                              "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                              uu____13067 uu____13068
                                             in
                                          (FStar_Errors.Fatal_MismatchedPatternType,
                                            uu____13066)
                                           in
                                        FStar_Errors.raise_error uu____13061
                                          exp1.FStar_Syntax_Syntax.pos)
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
                                   ((let uu____13085 =
                                       let uu____13086 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2
                                          in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____13086
                                        in
                                     if uu____13085
                                     then
                                       let unresolved =
                                         let uu____13098 =
                                           FStar_Util.set_difference uvs1
                                             uvs2
                                            in
                                         FStar_All.pipe_right uu____13098
                                           FStar_Util.set_elements
                                          in
                                       let uu____13125 =
                                         let uu____13130 =
                                           let uu____13131 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env norm_exp
                                              in
                                           let uu____13132 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env expected_pat_t
                                              in
                                           let uu____13133 =
                                             let uu____13134 =
                                               FStar_All.pipe_right
                                                 unresolved
                                                 (FStar_List.map
                                                    (fun uu____13152  ->
                                                       match uu____13152 with
                                                       | (u,uu____13158) ->
                                                           FStar_Syntax_Print.uvar_to_string
                                                             u))
                                                in
                                             FStar_All.pipe_right uu____13134
                                               (FStar_String.concat ", ")
                                              in
                                           FStar_Util.format3
                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                             uu____13131 uu____13132
                                             uu____13133
                                            in
                                         (FStar_Errors.Fatal_UnresolvedPatternVar,
                                           uu____13130)
                                          in
                                       FStar_Errors.raise_error uu____13125
                                         p.FStar_Syntax_Syntax.p
                                     else ());
                                    (let uu____13163 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High
                                        in
                                     if uu____13163
                                     then
                                       let uu____13164 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1
                                          in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____13164
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1
                                        in
                                     (p1, pat_bvs1, pat_env, exp1,
                                       guard_pat_annots, norm_exp)))))))
                    in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____13173 =
                   let uu____13180 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____13180
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____13173 with
                  | (scrutinee_env,uu____13204) ->
                      let uu____13209 = tc_pat true pat_t pattern  in
                      (match uu____13209 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____13250 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13272 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____13272
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____13286 =
                                      let uu____13293 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____13293 e  in
                                    match uu____13286 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____13250 with
                            | (when_clause1,g_when) ->
                                let uu____13327 = tc_term pat_env branch_exp
                                   in
                                (match uu____13327 with
                                 | (branch_exp1,c,g_branch) ->
                                     let g_branch1 =
                                       FStar_TypeChecker_Rel.conj_guard
                                         guard_pat_annots g_branch
                                        in
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____13360 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41) uu____13360
                                        in
                                     let uu____13363 =
                                       let eqs =
                                         let uu____13373 =
                                           let uu____13374 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____13374  in
                                         if uu____13373
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp
                                               in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13381 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13398 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13399 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13400 ->
                                                let uu____13401 =
                                                  let uu____13402 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13402 pat_t
                                                    scrutinee_tm e
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____13401)
                                          in
                                       let uu____13403 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1
                                          in
                                       match uu____13403 with
                                       | (c1,g_branch2) ->
                                           let uu____13418 =
                                             match (eqs, when_condition) with
                                             | uu____13431 when
                                                 let uu____13440 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____13440
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
                                                 let uu____13452 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____13453 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____13452, uu____13453)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____13462 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13462
                                                    in
                                                 let uu____13463 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____13464 =
                                                   let uu____13465 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13465 g_when
                                                    in
                                                 (uu____13463, uu____13464)
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
                                                 let uu____13473 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____13473, g_when)
                                              in
                                           (match uu____13418 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let uu____13485 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak
                                                   in
                                                let uu____13486 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak
                                                   in
                                                (uu____13485, uu____13486,
                                                  g_branch2))
                                        in
                                     (match uu____13363 with
                                      | (c1,g_when1,g_branch2) ->
                                          let branch_guard =
                                            let uu____13507 =
                                              let uu____13508 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____13508
                                               in
                                            if uu____13507
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13538 =
                                                     let uu____13539 =
                                                       let uu____13540 =
                                                         let uu____13543 =
                                                           let uu____13550 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13550
                                                            in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13543
                                                          in
                                                       FStar_List.length
                                                         uu____13540
                                                        in
                                                     uu____13539 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____13538
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____13556 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____13556 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13577 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         let disc1 =
                                                           let uu____13592 =
                                                             let uu____13593
                                                               =
                                                               let uu____13594
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____13594]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13593
                                                              in
                                                           uu____13592
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____13597 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool
                                                            in
                                                         [uu____13597]
                                                   else []  in
                                                 let fail uu____13602 =
                                                   let uu____13603 =
                                                     let uu____13604 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____13605 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1
                                                        in
                                                     let uu____13606 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13604
                                                       uu____13605
                                                       uu____13606
                                                      in
                                                   failwith uu____13603  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13617) ->
                                                       head_constructor t1
                                                   | uu____13622 -> fail ()
                                                    in
                                                 let pat_exp2 =
                                                   let uu____13624 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____13624
                                                     FStar_Syntax_Util.unmeta
                                                    in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13627 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13644;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13645;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13646;_},uu____13647)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13684 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____13686 =
                                                       let uu____13687 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13687
                                                         scrutinee_tm1
                                                         pat_exp2
                                                        in
                                                     [uu____13686]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13688 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____13696 =
                                                       let uu____13697 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13697
                                                        in
                                                     if uu____13696
                                                     then []
                                                     else
                                                       (let uu____13701 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13701)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____13704 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____13706 =
                                                       let uu____13707 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13707
                                                        in
                                                     if uu____13706
                                                     then []
                                                     else
                                                       (let uu____13711 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13711)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____13737 =
                                                       let uu____13738 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13738
                                                        in
                                                     if uu____13737
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____13745 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____13777
                                                                     ->
                                                                    match uu____13777
                                                                    with
                                                                    | 
                                                                    (ei,uu____13787)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____13793
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____13793
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____13814
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____13828
                                                                    =
                                                                    let uu____13829
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____13830
                                                                    =
                                                                    let uu____13831
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____13831]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____13829
                                                                    uu____13830
                                                                     in
                                                                    uu____13828
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13745
                                                            FStar_List.flatten
                                                           in
                                                        let uu____13840 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____13840
                                                          sub_term_guards)
                                                 | uu____13843 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____13855 =
                                                   let uu____13856 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____13856
                                                    in
                                                 if uu____13855
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____13859 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____13859
                                                       in
                                                    let uu____13864 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____13864 with
                                                    | (k,uu____13870) ->
                                                        let uu____13871 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____13871
                                                         with
                                                         | (t1,uu____13879,uu____13880)
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
                                              g_when1 g_branch2
                                             in
                                          ((let uu____13886 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____13886
                                            then
                                              let uu____13887 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____13887
                                            else ());
                                           (let uu____13889 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            (uu____13889, branch_guard, c1,
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
          let uu____13915 = check_let_bound_def true env1 lb  in
          (match uu____13915 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____13937 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13954 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____13954, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13957 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____13957
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____13961 =
                      let uu____13974 =
                        let uu____13989 =
                          let uu____13998 =
                            let uu____14011 = c1.FStar_Syntax_Syntax.comp ()
                               in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____14011)
                             in
                          [uu____13998]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____13989
                         in
                      FStar_List.hd uu____13974  in
                    match uu____13961 with
                    | (uu____14064,univs1,e11,c11,gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Rel.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta;
                               FStar_TypeChecker_Normalize.NoDeltaSteps;
                               FStar_TypeChecker_Normalize.CompressUvars;
                               FStar_TypeChecker_Normalize.NoFullNorm;
                               FStar_TypeChecker_Normalize.Exclude
                                 FStar_TypeChecker_Normalize.Zeta] env1)
                           in
                        let g13 =
                          FStar_TypeChecker_Rel.abstract_guard_n gvs g12  in
                        (g13, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11)))
                  in
               (match uu____13937 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____14087 =
                      let uu____14094 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____14094
                      then
                        let uu____14101 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____14101 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____14124 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____14124
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____14125 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____14125, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____14135 = c11.FStar_Syntax_Syntax.comp ()
                               in
                            FStar_All.pipe_right uu____14135
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1)
                             in
                          let e21 =
                            let uu____14143 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____14143
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
                    (match uu____14087 with
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
                         let uu____14167 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         (uu____14167,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____14182 -> failwith "Impossible"

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
            let uu___315_14213 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___315_14213.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___315_14213.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___315_14213.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___315_14213.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___315_14213.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___315_14213.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___315_14213.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___315_14213.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___315_14213.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___315_14213.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___315_14213.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___315_14213.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___315_14213.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___315_14213.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___315_14213.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___315_14213.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___315_14213.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___315_14213.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___315_14213.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___315_14213.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___315_14213.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___315_14213.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___315_14213.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___315_14213.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___315_14213.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___315_14213.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___315_14213.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___315_14213.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___315_14213.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___315_14213.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___315_14213.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___315_14213.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___315_14213.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____14214 =
            let uu____14225 =
              let uu____14226 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____14226 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____14225 lb  in
          (match uu____14214 with
           | (e1,uu____14248,c1,g1,annotated) ->
               let x =
                 let uu___316_14253 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___316_14253.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___316_14253.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 }  in
               let uu____14254 =
                 let uu____14259 =
                   let uu____14260 = FStar_Syntax_Syntax.mk_binder x  in
                   [uu____14260]  in
                 FStar_Syntax_Subst.open_term uu____14259 e2  in
               (match uu____14254 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb  in
                    let x1 = FStar_Pervasives_Native.fst xbinder  in
                    let uu____14279 =
                      let uu____14286 = FStar_TypeChecker_Env.push_bv env2 x1
                         in
                      tc_term uu____14286 e21  in
                    (match uu____14279 with
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
                           let uu____14305 =
                             let uu____14308 =
                               let uu____14309 =
                                 let uu____14322 =
                                   FStar_Syntax_Subst.close xb e23  in
                                 ((false, [lb1]), uu____14322)  in
                               FStar_Syntax_Syntax.Tm_let uu____14309  in
                             FStar_Syntax_Syntax.mk uu____14308  in
                           uu____14305 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ
                            in
                         let x_eq_e1 =
                           let uu____14336 =
                             let uu____14337 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ
                                in
                             let uu____14338 =
                               FStar_Syntax_Syntax.bv_to_name x1  in
                             FStar_Syntax_Util.mk_eq2 uu____14337
                               c1.FStar_Syntax_Syntax.res_typ uu____14338 e11
                              in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.NonTrivial _0_42)
                             uu____14336
                            in
                         let g21 =
                           let uu____14340 =
                             let uu____14341 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard uu____14341 g2
                              in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14340
                            in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                            in
                         let uu____14343 =
                           let uu____14344 =
                             FStar_TypeChecker_Env.expected_typ env2  in
                           FStar_Option.isSome uu____14344  in
                         if uu____14343
                         then
                           let tt =
                             let uu____14354 =
                               FStar_TypeChecker_Env.expected_typ env2  in
                             FStar_All.pipe_right uu____14354
                               FStar_Option.get
                              in
                           ((let uu____14360 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____14360
                             then
                               let uu____14361 =
                                 FStar_Syntax_Print.term_to_string tt  in
                               let uu____14362 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14361 uu____14362
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                               in
                            (let uu____14367 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____14367
                             then
                               let uu____14368 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               let uu____14369 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____14368 uu____14369
                             else ());
                            (e4,
                              ((let uu___317_14372 = cres  in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___317_14372.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___317_14372.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___317_14372.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____14373 -> failwith "Impossible"

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
          let uu____14405 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14405 with
           | (lbs1,e21) ->
               let uu____14424 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14424 with
                | (env0,topt) ->
                    let uu____14443 = build_let_rec_env true env0 lbs1  in
                    (match uu____14443 with
                     | (lbs2,rec_env) ->
                         let uu____14462 = check_let_recs rec_env lbs2  in
                         (match uu____14462 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14482 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____14482
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____14488 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____14488
                                  (fun _0_43  ->
                                     FStar_Pervasives_Native.Some _0_43)
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
                                     let uu____14537 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14577 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14577)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14537
                                      in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____14626  ->
                                           match uu____14626 with
                                           | (x,uvs,e,c,gvs) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e)))
                                 in
                              let cres =
                                let uu____14673 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14673
                                 in
                              let uu____14678 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____14678 with
                               | (lbs5,e22) ->
                                   ((let uu____14698 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____14698
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____14699 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____14699, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____14712 -> failwith "Impossible"

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
          let uu____14744 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14744 with
           | (lbs1,e21) ->
               let uu____14763 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14763 with
                | (env0,topt) ->
                    let uu____14782 = build_let_rec_env false env0 lbs1  in
                    (match uu____14782 with
                     | (lbs2,rec_env) ->
                         let uu____14801 = check_let_recs rec_env lbs2  in
                         (match uu____14801 with
                          | (lbs3,g_lbs) ->
                              let uu____14820 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___318_14843 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___318_14843.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___318_14843.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___319_14845 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___319_14845.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___319_14845.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___319_14845.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___319_14845.FStar_Syntax_Syntax.lbdef)
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
                              (match uu____14820 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____14872 = tc_term env2 e21  in
                                   (match uu____14872 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____14889 =
                                            let uu____14890 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____14890 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____14889
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
                                          let uu___320_14894 = cres1  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___320_14894.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___320_14894.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___320_14894.FStar_Syntax_Syntax.comp)
                                          }  in
                                        let uu____14895 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____14895 with
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
                                                  uu____14931 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  let cres3 =
                                                    let uu___321_14936 =
                                                      cres2  in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___321_14936.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___321_14936.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___321_14936.FStar_Syntax_Syntax.comp)
                                                    }  in
                                                  (e, cres3, guard)))))))))
      | uu____14939 -> failwith "Impossible"

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
          let uu____14968 = FStar_Options.ml_ish ()  in
          if uu____14968
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____14971 =
               let uu____14976 =
                 let uu____14977 = FStar_Syntax_Subst.compress t  in
                 uu____14977.FStar_Syntax_Syntax.n  in
               let uu____14980 =
                 let uu____14981 = FStar_Syntax_Subst.compress lbdef  in
                 uu____14981.FStar_Syntax_Syntax.n  in
               (uu____14976, uu____14980)  in
             match uu____14971 with
             | (FStar_Syntax_Syntax.Tm_arrow
                (formals,c),FStar_Syntax_Syntax.Tm_abs
                (actuals,uu____14987,uu____14988)) ->
                 let actuals1 =
                   let uu____15026 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp  in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____15026 actuals
                    in
                 (if
                    (FStar_List.length formals) <>
                      (FStar_List.length actuals1)
                  then
                    (let actuals_msg =
                       let n1 = FStar_List.length actuals1  in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument was found"
                       else
                         (let uu____15047 = FStar_Util.string_of_int n1  in
                          FStar_Util.format1 "%s arguments were found"
                            uu____15047)
                        in
                     let formals_msg =
                       let n1 = FStar_List.length formals  in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument"
                       else
                         (let uu____15065 = FStar_Util.string_of_int n1  in
                          FStar_Util.format1 "%s arguments" uu____15065)
                        in
                     let msg =
                       let uu____15073 =
                         FStar_Syntax_Print.term_to_string lbtyp  in
                       let uu____15074 =
                         FStar_Syntax_Print.lbname_to_string lbname  in
                       FStar_Util.format4
                         "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                         uu____15073 uu____15074 formals_msg actuals_msg
                        in
                     FStar_Util.print1 "%s\n" msg)
                  else ();
                  (let quals =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       (FStar_Syntax_Util.comp_effect_name c)
                      in
                   FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
             | uu____15081 ->
                 let uu____15086 =
                   let uu____15091 =
                     let uu____15092 =
                       FStar_Syntax_Print.term_to_string lbdef  in
                     let uu____15093 =
                       FStar_Syntax_Print.term_to_string lbtyp  in
                     FStar_Util.format2
                       "Only function literals with arrow types can be defined recursively; got %s : %s"
                       uu____15092 uu____15093
                      in
                   (FStar_Errors.Fatal_RecursiveFunctionLiteral, uu____15091)
                    in
                 FStar_Errors.raise_error uu____15086
                   lbtyp.FStar_Syntax_Syntax.pos)
           in
        let uu____15094 =
          FStar_List.fold_left
            (fun uu____15120  ->
               fun lb  ->
                 match uu____15120 with
                 | (lbs1,env1) ->
                     let uu____15140 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____15140 with
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
                              (let uu____15160 =
                                 let uu____15167 =
                                   let uu____15168 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15168
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___322_15179 = env0  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___322_15179.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___322_15179.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___322_15179.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___322_15179.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___322_15179.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___322_15179.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___322_15179.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___322_15179.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___322_15179.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___322_15179.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___322_15179.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___322_15179.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___322_15179.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___322_15179.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___322_15179.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___322_15179.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___322_15179.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___322_15179.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___322_15179.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___322_15179.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___322_15179.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___322_15179.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___322_15179.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___322_15179.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___322_15179.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___322_15179.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___322_15179.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___322_15179.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___322_15179.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___322_15179.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___322_15179.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___322_15179.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___322_15179.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____15167
                                  in
                               match uu____15160 with
                               | (t1,uu____15181,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let uu____15185 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____15185);
                                    norm env0 t1))
                             in
                          let env3 =
                            let uu____15187 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1
                               in
                            if uu____15187
                            then
                              let uu___323_15188 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___323_15188.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___323_15188.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___323_15188.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___323_15188.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___323_15188.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___323_15188.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___323_15188.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___323_15188.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___323_15188.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___323_15188.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___323_15188.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___323_15188.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___323_15188.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___323_15188.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___323_15188.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___323_15188.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___323_15188.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___323_15188.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___323_15188.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___323_15188.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___323_15188.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___323_15188.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___323_15188.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___323_15188.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___323_15188.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___323_15188.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___323_15188.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___323_15188.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___323_15188.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___323_15188.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___323_15188.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___323_15188.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___323_15188.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1)
                             in
                          let lb1 =
                            let uu___324_15205 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___324_15205.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___324_15205.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____15094 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____15228 =
        let uu____15237 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____15266 =
                     let uu____15267 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef
                        in
                     uu____15267.FStar_Syntax_Syntax.n  in
                   match uu____15266 with
                   | FStar_Syntax_Syntax.Tm_abs uu____15270 -> ()
                   | uu____15287 ->
                       let uu____15288 =
                         FStar_Syntax_Syntax.range_of_lbname
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                           "Only function literals may be defined recursively")
                         uu____15288);
                  (let uu____15289 =
                     let uu____15296 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp
                        in
                     tc_tot_or_gtot_term uu____15296
                       lb.FStar_Syntax_Syntax.lbdef
                      in
                   match uu____15289 with
                   | (e,c,g) ->
                       ((let uu____15305 =
                           let uu____15306 =
                             FStar_Syntax_Util.is_total_lcomp c  in
                           Prims.op_Negation uu____15306  in
                         if uu____15305
                         then
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedGTotForLetRec,
                               "Expected let rec to be a Tot term; got effect GTot")
                             e.FStar_Syntax_Syntax.pos
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
        FStar_All.pipe_right uu____15237 FStar_List.unzip  in
      match uu____15228 with
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
        let uu____15355 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____15355 with
        | (env1,uu____15373) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____15381 = check_lbtyp top_level env lb  in
            (match uu____15381 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____15425 =
                     tc_maybe_toplevel_term
                       (let uu___325_15434 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___325_15434.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___325_15434.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___325_15434.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___325_15434.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___325_15434.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___325_15434.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___325_15434.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___325_15434.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___325_15434.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___325_15434.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___325_15434.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___325_15434.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___325_15434.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___325_15434.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___325_15434.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___325_15434.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___325_15434.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___325_15434.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___325_15434.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___325_15434.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___325_15434.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___325_15434.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___325_15434.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___325_15434.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___325_15434.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___325_15434.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___325_15434.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___325_15434.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___325_15434.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___325_15434.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___325_15434.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___325_15434.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___325_15434.FStar_TypeChecker_Env.dep_graph)
                        }) e11
                      in
                   match uu____15425 with
                   | (e12,c1,g1) ->
                       let uu____15448 =
                         let uu____15453 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15457  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15453 e12 c1 wf_annot
                          in
                       (match uu____15448 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____15472 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____15472
                              then
                                let uu____15473 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____15474 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____15475 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____15473 uu____15474 uu____15475
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
            let uu____15509 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15509 with
             | (univ_opening,univ_vars1) ->
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, env))
        | uu____15548 ->
            let uu____15549 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15549 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15598 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15598)
                 else
                   (let uu____15606 = FStar_Syntax_Util.type_u ()  in
                    match uu____15606 with
                    | (k,uu____15626) ->
                        let uu____15627 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____15627 with
                         | (t2,uu____15649,g) ->
                             ((let uu____15652 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____15652
                               then
                                 let uu____15653 =
                                   let uu____15654 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____15654
                                    in
                                 let uu____15655 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15653 uu____15655
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____15658 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15658))))))

and tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____15666  ->
      match uu____15666 with
      | (x,imp) ->
          let uu____15685 = FStar_Syntax_Util.type_u ()  in
          (match uu____15685 with
           | (tu,u) ->
               ((let uu____15705 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____15705
                 then
                   let uu____15706 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____15707 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____15708 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____15706 uu____15707 uu____15708
                 else ());
                (let uu____15710 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____15710 with
                 | (t,uu____15730,g) ->
                     let x1 =
                       ((let uu___326_15738 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___326_15738.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___326_15738.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____15740 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____15740
                       then
                         let uu____15741 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____15742 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____15741 uu____15742
                       else ());
                      (let uu____15744 = push_binding env x1  in
                       (x1, uu____15744, g, u))))))

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
            let uu____15834 = tc_binder env1 b  in
            (match uu____15834 with
             | (b1,env',g,u) ->
                 let uu____15875 = aux env' bs2  in
                 (match uu____15875 with
                  | (bs3,env'1,g',us) ->
                      let uu____15928 =
                        let uu____15929 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g uu____15929  in
                      ((b1 :: bs3), env'1, uu____15928, (u :: us))))
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
          (fun uu____16014  ->
             fun uu____16015  ->
               match (uu____16014, uu____16015) with
               | ((t,imp),(args1,g)) ->
                   let uu____16084 = tc_term env1 t  in
                   (match uu____16084 with
                    | (t1,uu____16102,g') ->
                        let uu____16104 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____16104))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16146  ->
             match uu____16146 with
             | (pats1,g) ->
                 let uu____16171 = tc_args env p  in
                 (match uu____16171 with
                  | (args,g') ->
                      let uu____16184 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____16184))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____16197 = tc_maybe_toplevel_term env e  in
      match uu____16197 with
      | (e1,c,g) ->
          let uu____16213 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____16213
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = c.FStar_Syntax_Syntax.comp ()  in
             let c2 = norm_c env c1  in
             let uu____16226 =
               let uu____16231 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____16231
               then
                 let uu____16236 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____16236, false)
               else
                 (let uu____16238 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____16238, true))
                in
             match uu____16226 with
             | (target_comp,allow_ghost) ->
                 let uu____16247 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____16247 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16257 =
                        FStar_TypeChecker_Rel.conj_guard g1 g'  in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____16257)
                  | uu____16258 ->
                      if allow_ghost
                      then
                        let uu____16267 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____16267
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____16279 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____16279
                           e1.FStar_Syntax_Syntax.pos)))

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
      let uu____16302 = tc_tot_or_gtot_term env t  in
      match uu____16302 with
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
      (let uu____16330 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____16330
       then
         let uu____16331 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____16331
       else ());
      (let env1 =
         let uu___327_16334 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___327_16334.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___327_16334.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___327_16334.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___327_16334.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___327_16334.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___327_16334.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___327_16334.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___327_16334.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___327_16334.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___327_16334.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___327_16334.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___327_16334.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___327_16334.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___327_16334.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___327_16334.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___327_16334.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___327_16334.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___327_16334.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___327_16334.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___327_16334.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___327_16334.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___327_16334.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___327_16334.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___327_16334.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___327_16334.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___327_16334.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___327_16334.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___327_16334.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___327_16334.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___327_16334.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___327_16334.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___327_16334.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____16341 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____16376) ->
             let uu____16377 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____16377
          in
       match uu____16341 with
       | (t,c,g) ->
           let uu____16393 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____16393
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16403 =
                let uu____16408 =
                  let uu____16409 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____16409
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____16408)
                 in
              let uu____16410 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____16403 uu____16410))
  
let level_of_type_fail :
  'Auu____16421 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16421
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16434 =
          let uu____16439 =
            let uu____16440 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____16440 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____16439)  in
        let uu____16441 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____16434 uu____16441
  
let level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16458 =
            let uu____16459 = FStar_Syntax_Util.unrefine t1  in
            uu____16459.FStar_Syntax_Syntax.n  in
          match uu____16458 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16463 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____16466 = FStar_Syntax_Util.type_u ()  in
                 match uu____16466 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___330_16474 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___330_16474.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___330_16474.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___330_16474.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___330_16474.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___330_16474.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___330_16474.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___330_16474.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___330_16474.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___330_16474.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___330_16474.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___330_16474.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___330_16474.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___330_16474.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___330_16474.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___330_16474.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___330_16474.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___330_16474.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___330_16474.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___330_16474.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___330_16474.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___330_16474.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___330_16474.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___330_16474.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___330_16474.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___330_16474.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___330_16474.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___330_16474.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___330_16474.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___330_16474.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___330_16474.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___330_16474.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___330_16474.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___330_16474.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16478 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____16478
                       | uu____16479 ->
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
      let uu____16488 =
        let uu____16489 = FStar_Syntax_Subst.compress e  in
        uu____16489.FStar_Syntax_Syntax.n  in
      match uu____16488 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16494 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16499 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16526 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16542) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16565,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16592) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16599 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16599 with | ((uu____16610,t),uu____16612) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16617,(FStar_Util.Inl t,uu____16619),uu____16620) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16667,(FStar_Util.Inr c,uu____16669),uu____16670) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____16720;
             FStar_Syntax_Syntax.vars = uu____16721;_},us)
          ->
          let uu____16727 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16727 with
           | ((us',t),uu____16740) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____16746 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____16746)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____16762 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____16763 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____16773) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____16796 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____16796 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____16816  ->
                      match uu____16816 with
                      | (b,uu____16822) ->
                          let uu____16823 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____16823) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____16828 = universe_of_aux env res  in
                 level_of_type env res uu____16828  in
               let u_c =
                 let uu____16830 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____16830 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____16834 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____16834
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
            | FStar_Syntax_Syntax.Tm_bvar uu____16927 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____16942 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____16981 ->
                let uu____16982 = universe_of_aux env hd3  in
                (uu____16982, args1)
            | FStar_Syntax_Syntax.Tm_name uu____16995 ->
                let uu____16996 = universe_of_aux env hd3  in
                (uu____16996, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____17009 ->
                let uu____17026 = universe_of_aux env hd3  in
                (uu____17026, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____17039 ->
                let uu____17046 = universe_of_aux env hd3  in
                (uu____17046, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17059 ->
                let uu____17086 = universe_of_aux env hd3  in
                (uu____17086, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17099 ->
                let uu____17106 = universe_of_aux env hd3  in
                (uu____17106, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17119 ->
                let uu____17120 = universe_of_aux env hd3  in
                (uu____17120, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17133 ->
                let uu____17146 = universe_of_aux env hd3  in
                (uu____17146, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17159 ->
                let uu____17166 = universe_of_aux env hd3  in
                (uu____17166, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17179 ->
                let uu____17180 = universe_of_aux env hd3  in
                (uu____17180, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____17193,hd4::uu____17195) ->
                let uu____17260 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____17260 with
                 | (uu____17275,uu____17276,hd5) ->
                     let uu____17294 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____17294 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17345 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____17347 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____17347 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17398 ->
                let uu____17399 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____17399 with
                 | (env1,uu____17421) ->
                     let env2 =
                       let uu___331_17427 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___331_17427.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___331_17427.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___331_17427.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___331_17427.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___331_17427.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___331_17427.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___331_17427.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___331_17427.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___331_17427.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___331_17427.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___331_17427.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___331_17427.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___331_17427.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___331_17427.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___331_17427.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___331_17427.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___331_17427.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___331_17427.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___331_17427.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___331_17427.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___331_17427.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___331_17427.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___331_17427.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___331_17427.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___331_17427.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___331_17427.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___331_17427.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___331_17427.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___331_17427.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___331_17427.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___331_17427.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     ((let uu____17429 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____17429
                       then
                         let uu____17430 =
                           let uu____17431 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____17431  in
                         let uu____17432 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17430 uu____17432
                       else ());
                      (let uu____17434 = tc_term env2 hd3  in
                       match uu____17434 with
                       | (uu____17455,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17456;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17458;
                                        FStar_Syntax_Syntax.comp =
                                          uu____17459;_},g)
                           ->
                           ((let uu____17470 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____17470
                               FStar_Pervasives.ignore);
                            (t, args1)))))
             in
          let uu____17481 = type_of_head true hd1 args  in
          (match uu____17481 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____17521 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____17521 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17565 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____17565)))
      | FStar_Syntax_Syntax.Tm_match (uu____17568,hd1::uu____17570) ->
          let uu____17635 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____17635 with
           | (uu____17638,uu____17639,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17657,[]) ->
          level_of_type_fail env e "empty match cases"
  
let universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____17700 = universe_of_aux env e  in
      level_of_type env e uu____17700
  
let tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____17719 = tc_binders env tps  in
      match uu____17719 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
  