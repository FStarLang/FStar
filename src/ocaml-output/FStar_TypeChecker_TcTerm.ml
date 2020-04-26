open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___8_5 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___8_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___8_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___8_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___8_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___8_5.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___8_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___8_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___8_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___8_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___8_5.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___8_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___8_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___8_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___8_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___8_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___8_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.use_eq_strict =
        (uu___8_5.FStar_TypeChecker_Env.use_eq_strict);
      FStar_TypeChecker_Env.is_iface =
        (uu___8_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___8_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___8_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___8_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 = (uu___8_5.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___8_5.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___8_5.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___8_5.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___8_5.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___8_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___8_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___8_5.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___8_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___8_5.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___8_5.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___8_5.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___8_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___8_5.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.try_solve_implicits_hook =
        (uu___8_5.FStar_TypeChecker_Env.try_solve_implicits_hook);
      FStar_TypeChecker_Env.splice = (uu___8_5.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.mpreprocess =
        (uu___8_5.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___8_5.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.identifier_info =
        (uu___8_5.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___8_5.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___8_5.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___8_5.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___8_5.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___8_5.FStar_TypeChecker_Env.erasable_types_tab)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___11_13 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___11_13.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___11_13.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___11_13.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___11_13.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___11_13.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___11_13.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___11_13.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___11_13.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___11_13.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___11_13.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___11_13.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___11_13.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___11_13.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___11_13.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___11_13.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___11_13.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.use_eq_strict =
        (uu___11_13.FStar_TypeChecker_Env.use_eq_strict);
      FStar_TypeChecker_Env.is_iface =
        (uu___11_13.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___11_13.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___11_13.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___11_13.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___11_13.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___11_13.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___11_13.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___11_13.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___11_13.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___11_13.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___11_13.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___11_13.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___11_13.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___11_13.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___11_13.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___11_13.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___11_13.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___11_13.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.try_solve_implicits_hook =
        (uu___11_13.FStar_TypeChecker_Env.try_solve_implicits_hook);
      FStar_TypeChecker_Env.splice =
        (uu___11_13.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.mpreprocess =
        (uu___11_13.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___11_13.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.identifier_info =
        (uu___11_13.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___11_13.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___11_13.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___11_13.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___11_13.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___11_13.FStar_TypeChecker_Env.erasable_types_tab)
    }
  
let (mk_lex_list :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
           let uu____49 =
             let uu____54 =
               let uu____55 = FStar_Syntax_Syntax.as_arg v  in
               let uu____64 =
                 let uu____75 = FStar_Syntax_Syntax.as_arg tl  in [uu____75]
                  in
               uu____55 :: uu____64  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____54
              in
           uu____49 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___0_116  ->
    match uu___0_116 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____121 -> false
  
let steps : 'uuuuuu130 . 'uuuuuu130 -> FStar_TypeChecker_Env.step Prims.list
  =
  fun env  ->
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.NoFullNorm]
  
let (norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> FStar_TypeChecker_Normalize.normalize (steps env) env t
  
let (norm_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
  
let (check_no_escape :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____218 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____232 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____232 with
                 | FStar_Pervasives_Native.None  ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____259 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____263 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____263
                            | FStar_Pervasives_Native.Some head ->
                                let uu____267 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____269 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____267 uu____269
                             in
                          let uu____272 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____272
                           in
                        let uu____278 =
                          let uu____291 = FStar_TypeChecker_Env.get_range env
                             in
                          let uu____292 =
                            let uu____293 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____293
                             in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____291 env uu____292
                           in
                        match uu____278 with
                        | (s,uu____308,g0) ->
                            let uu____322 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s  in
                            (match uu____322 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____332 =
                                     FStar_TypeChecker_Env.conj_guard g g0
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____332
                                    in
                                 (s, g1)
                             | uu____333 -> fail ())))
             in
          aux false kt
  
let push_binding :
  'uuuuuu344 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu344) -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
  
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s  ->
    fun b  ->
      fun v  ->
        let uu____399 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____399
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v)) ::
          s
  
let (set_lcomp_result :
  FStar_TypeChecker_Common.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_TypeChecker_Common.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_TypeChecker_Common.apply_lcomp
        (fun c  -> FStar_Syntax_Util.set_result_typ c t) (fun g  -> g)
        (let uu___66_429 = lc  in
         {
           FStar_TypeChecker_Common.eff_name =
             (uu___66_429.FStar_TypeChecker_Common.eff_name);
           FStar_TypeChecker_Common.res_typ = t;
           FStar_TypeChecker_Common.cflags =
             (uu___66_429.FStar_TypeChecker_Common.cflags);
           FStar_TypeChecker_Common.comp_thunk =
             (uu___66_429.FStar_TypeChecker_Common.comp_thunk)
         })
  
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> e 
let (maybe_warn_on_use :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv -> unit) =
  fun env  ->
    fun fv  ->
      let uu____452 =
        FStar_TypeChecker_Env.lookup_attrs_of_lid env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      match uu____452 with
      | FStar_Pervasives_Native.None  -> ()
      | FStar_Pervasives_Native.Some attrs ->
          FStar_All.pipe_right attrs
            (FStar_List.iter
               (fun a  ->
                  let uu____475 = FStar_Syntax_Util.head_and_args a  in
                  match uu____475 with
                  | (head,args) ->
                      let msg_arg m =
                        match args with
                        | ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_string (s,uu____529));
                             FStar_Syntax_Syntax.pos = uu____530;
                             FStar_Syntax_Syntax.vars = uu____531;_},uu____532)::[]
                            -> Prims.op_Hat m (Prims.op_Hat ": " s)
                        | uu____560 -> m  in
                      (match head.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar attr_fv when
                           FStar_Ident.lid_equals
                             (attr_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.warn_on_use_attr
                           ->
                           let m =
                             let uu____574 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Util.format1
                               "Every use of %s triggers a warning" uu____574
                              in
                           let uu____577 =
                             FStar_Ident.range_of_lid
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              in
                           FStar_Errors.log_issue uu____577
                             (FStar_Errors.Warning_WarnOnUse, (msg_arg m))
                       | FStar_Syntax_Syntax.Tm_fvar attr_fv when
                           FStar_Ident.lid_equals
                             (attr_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let m =
                             let uu____582 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Util.format1 "%s is deprecated" uu____582
                              in
                           let uu____585 =
                             FStar_Ident.range_of_lid
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              in
                           FStar_Errors.log_issue uu____585
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               (msg_arg m))
                       | uu____587 -> ())))
  
let (value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_TypeChecker_Common.lcomp)
        FStar_Util.either ->
        FStar_TypeChecker_Common.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos
            "value_check_expected_typ" env guard;
          (let lc =
             match tlc with
             | FStar_Util.Inl t ->
                 let uu____633 = FStar_Syntax_Syntax.mk_Total t  in
                 FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                   uu____633
             | FStar_Util.Inr lc -> lc  in
           let t = lc.FStar_TypeChecker_Common.res_typ  in
           let uu____636 =
             let uu____643 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____643 with
             | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____653 =
                   FStar_TypeChecker_Util.check_has_type env e lc t'  in
                 (match uu____653 with
                  | (e1,lc1,g) ->
                      ((let uu____670 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Medium
                           in
                        if uu____670
                        then
                          let uu____673 =
                            FStar_TypeChecker_Common.lcomp_to_string lc1  in
                          let uu____675 =
                            FStar_Syntax_Print.term_to_string t'  in
                          let uu____677 =
                            FStar_TypeChecker_Rel.guard_to_string env g  in
                          let uu____679 =
                            FStar_TypeChecker_Rel.guard_to_string env guard
                             in
                          FStar_Util.print4
                            "value_check_expected_typ: type is %s<:%s \tguard is %s, %s\n"
                            uu____673 uu____675 uu____677 uu____679
                        else ());
                       (let t1 = lc1.FStar_TypeChecker_Common.res_typ  in
                        let g1 = FStar_TypeChecker_Env.conj_guard g guard  in
                        let msg =
                          let uu____693 =
                            FStar_TypeChecker_Env.is_trivial_guard_formula g1
                             in
                          if uu____693
                          then FStar_Pervasives_Native.None
                          else
                            FStar_All.pipe_left
                              (fun uu____722  ->
                                 FStar_Pervasives_Native.Some uu____722)
                              (FStar_TypeChecker_Err.subtyping_failed env t1
                                 t')
                           in
                        let uu____723 =
                          FStar_TypeChecker_Util.strengthen_precondition msg
                            env e1 lc1 g1
                           in
                        match uu____723 with
                        | (lc2,g2) ->
                            let uu____736 = set_lcomp_result lc2 t'  in
                            ((memo_tk e1 t'), uu____736, g2))))
              in
           match uu____636 with | (e1,lc1,g) -> (e1, lc1, g))
  
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____774 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____774 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____784 = FStar_TypeChecker_Util.maybe_coerce_lc env e lc t
               in
            (match uu____784 with
             | (e1,lc1,g_c) ->
                 let uu____800 =
                   FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t  in
                 (match uu____800 with
                  | (e2,lc2,g) ->
                      let uu____816 = FStar_TypeChecker_Env.conj_guard g g_c
                         in
                      (e2, lc2, uu____816)))
  
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun copt  ->
      fun ec  ->
        let uu____857 = ec  in
        match uu____857 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____880 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____880
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____885 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____885
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____891 =
              let ct = FStar_Syntax_Util.comp_result c  in
              match copt with
              | FStar_Pervasives_Native.Some uu____915 ->
                  (copt, c, FStar_Pervasives_Native.None)
              | FStar_Pervasives_Native.None  ->
                  let uu____920 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____923 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____923))
                     in
                  if uu____920
                  then
                    let uu____936 =
                      let uu____939 =
                        FStar_Syntax_Util.ml_comp ct
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____939  in
                    (uu____936, c, FStar_Pervasives_Native.None)
                  else
                    (let uu____946 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____946
                     then
                       let uu____959 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____959,
                         FStar_Pervasives_Native.None)
                     else
                       (let uu____966 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____966
                        then
                          let uu____979 =
                            let uu____982 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____982  in
                          (uu____979, c, FStar_Pervasives_Native.None)
                        else
                          (let uu____989 =
                             let uu____991 =
                               FStar_All.pipe_right
                                 (FStar_Syntax_Util.comp_effect_name c)
                                 (FStar_TypeChecker_Env.norm_eff_name env)
                                in
                             FStar_All.pipe_right uu____991
                               (FStar_TypeChecker_Env.is_layered_effect env)
                              in
                           if uu____989
                           then
                             let uu____1004 =
                               let uu____1010 =
                                 let uu____1012 =
                                   let uu____1014 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name
                                      in
                                   FStar_All.pipe_right uu____1014
                                     FStar_Ident.string_of_lid
                                    in
                                 let uu____1018 =
                                   FStar_Range.string_of_range
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_Util.format2
                                   "Missing annotation for a layered effect (%s) computation at %s"
                                   uu____1012 uu____1018
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____1010)  in
                             FStar_Errors.raise_error uu____1004
                               e.FStar_Syntax_Syntax.pos
                           else
                             (let uu____1034 =
                                FStar_Options.trivial_pre_for_unannotated_effectful_fns
                                  ()
                                 in
                              if uu____1034
                              then
                                let uu____1047 =
                                  let uu____1050 =
                                    FStar_TypeChecker_Util.check_trivial_precondition
                                      env c
                                     in
                                  match uu____1050 with
                                  | (uu____1059,uu____1060,g) ->
                                      FStar_Pervasives_Native.Some g
                                   in
                                (FStar_Pervasives_Native.None, c, uu____1047)
                              else
                                (FStar_Pervasives_Native.None, c,
                                  FStar_Pervasives_Native.None)))))
               in
            (match uu____891 with
             | (expected_c_opt,c1,gopt) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2,
                        ((match gopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_TypeChecker_Env.trivial_guard
                          | FStar_Pervasives_Native.Some g -> g)))
                  | FStar_Pervasives_Native.Some expected_c ->
                      ((match gopt with
                        | FStar_Pervasives_Native.None  -> ()
                        | FStar_Pervasives_Native.Some uu____1099 ->
                            failwith
                              "Impossible! check_expected_effect, gopt should have been None");
                       (let c3 =
                          let uu____1102 =
                            FStar_TypeChecker_Common.lcomp_of_comp c2  in
                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                            env e uu____1102
                           in
                        let uu____1103 =
                          FStar_TypeChecker_Common.lcomp_comp c3  in
                        match uu____1103 with
                        | (c4,g_c) ->
                            ((let uu____1117 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Medium
                                 in
                              if uu____1117
                              then
                                let uu____1121 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____1123 =
                                  FStar_Syntax_Print.comp_to_string c4  in
                                let uu____1125 =
                                  FStar_Syntax_Print.comp_to_string
                                    expected_c
                                   in
                                FStar_Util.print3
                                  "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                                  uu____1121 uu____1123 uu____1125
                              else ());
                             (let uu____1130 =
                                FStar_TypeChecker_Util.check_comp env e c4
                                  expected_c
                                 in
                              match uu____1130 with
                              | (e1,uu____1144,g) ->
                                  let g1 =
                                    let uu____1147 =
                                      FStar_TypeChecker_Env.get_range env  in
                                    FStar_TypeChecker_Util.label_guard
                                      uu____1147
                                      "could not prove post-condition" g
                                     in
                                  ((let uu____1150 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Medium
                                       in
                                    if uu____1150
                                    then
                                      let uu____1153 =
                                        FStar_Range.string_of_range
                                          e1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____1155 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          env g1
                                         in
                                      FStar_Util.print2
                                        "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                        uu____1153 uu____1155
                                    else ());
                                   (let e2 =
                                      FStar_TypeChecker_Util.maybe_lift env
                                        e1
                                        (FStar_Syntax_Util.comp_effect_name
                                           c4)
                                        (FStar_Syntax_Util.comp_effect_name
                                           expected_c)
                                        (FStar_Syntax_Util.comp_result c4)
                                       in
                                    let uu____1161 =
                                      FStar_TypeChecker_Env.conj_guard g_c g1
                                       in
                                    (e2, expected_c, uu____1161)))))))))
  
let no_logical_guard :
  'uuuuuu1171 'uuuuuu1172 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1171 * 'uuuuuu1172 * FStar_TypeChecker_Env.guard_t) ->
        ('uuuuuu1171 * 'uuuuuu1172 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____1194  ->
      match uu____1194 with
      | (te,kt,f) ->
          let uu____1204 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____1204 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____1212 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____1218 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____1212 uu____1218)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____1231 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____1231 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____1236 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____1236
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1266 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1266 with
        | (head,args) ->
            let uu____1311 =
              let uu____1326 =
                let uu____1327 = FStar_Syntax_Util.un_uinst head  in
                uu____1327.FStar_Syntax_Syntax.n  in
              (uu____1326, args)  in
            (match uu____1311 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1343) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1370,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1371))::(hd,FStar_Pervasives_Native.None
                                                                 )::(tl,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let hdvs = get_pat_vars' all false hd  in
                 let tlvs = get_pat_vars' all andlist tl  in
                 if andlist
                 then FStar_Util.set_intersect hdvs tlvs
                 else FStar_Util.set_union hdvs tlvs
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1448,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1449))::(pat,FStar_Pervasives_Native.None
                                                                 )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> FStar_Syntax_Free.names pat
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> get_pat_vars' all true subpats
             | uu____1533 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
  
let (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats 
let check_pat_fvs :
  'uuuuuu1577 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'uuuuuu1577) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1613 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1620 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1613 uu____1620  in
          let uu____1621 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1648  ->
                    match uu____1648 with
                    | (b,uu____1655) ->
                        let uu____1656 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1656))
             in
          match uu____1621 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1663) ->
              let uu____1668 =
                let uu____1674 =
                  let uu____1676 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1676
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1674)  in
              FStar_Errors.log_issue rng uu____1668
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1702 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1702 with
        | (head,args) ->
            let uu____1747 =
              let uu____1762 =
                let uu____1763 = FStar_Syntax_Util.un_uinst head  in
                uu____1763.FStar_Syntax_Syntax.n  in
              (uu____1762, args)  in
            (match uu____1747 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1779) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1801::(hd,uu____1803)::(tl,uu____1805)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1872 = pat_terms hd  in
                 let uu____1875 = pat_terms tl  in
                 FStar_List.append uu____1872 uu____1875
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1879::(pat,uu____1881)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1966 -> [])
         in
      let rec aux t1 =
        let uu____1991 =
          let uu____1992 = FStar_Syntax_Subst.compress t1  in
          uu____1992.FStar_Syntax_Syntax.n  in
        match uu____1991 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1997 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1998 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1999 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____2000 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____2013 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_constant uu____2014 -> [t1]
        | FStar_Syntax_Syntax.Tm_abs uu____2015 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____2034 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____2049 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____2056 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____2079 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____2093 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____2108 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____2116 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____2116 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____2149 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____2166  ->
                   match uu____2166 with
                   | (t3,uu____2178) ->
                       let uu____2183 = aux t3  in
                       FStar_List.append acc uu____2183) uu____2149 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2187,uu____2188) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2230) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2236) -> aux t2  in
      let tlist =
        let uu____2244 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____2244 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = Prims.int_zero
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____2267 =
                    let uu____2269 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____2269  in
                  Prims.op_Hat s uu____2267) "" tlist
            in
         let uu____2273 =
           let uu____2279 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2279)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2273)
  
let check_smt_pat :
  'uuuuuu2294 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu2294) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2335 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2335
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2338;
                  FStar_Syntax_Syntax.effect_name = uu____2339;
                  FStar_Syntax_Syntax.result_typ = uu____2340;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2344)::[];
                  FStar_Syntax_Syntax.flags = uu____2345;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2407 -> failwith "Impossible"
          else ()
  
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env  in
            let env1 =
              let uu___396_2470 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___396_2470.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___396_2470.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___396_2470.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___396_2470.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___396_2470.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___396_2470.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___396_2470.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___396_2470.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___396_2470.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___396_2470.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___396_2470.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___396_2470.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___396_2470.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___396_2470.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___396_2470.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___396_2470.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.use_eq_strict =
                  (uu___396_2470.FStar_TypeChecker_Env.use_eq_strict);
                FStar_TypeChecker_Env.is_iface =
                  (uu___396_2470.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___396_2470.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___396_2470.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___396_2470.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___396_2470.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___396_2470.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___396_2470.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___396_2470.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___396_2470.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___396_2470.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___396_2470.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___396_2470.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___396_2470.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___396_2470.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___396_2470.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___396_2470.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___396_2470.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___396_2470.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.try_solve_implicits_hook =
                  (uu___396_2470.FStar_TypeChecker_Env.try_solve_implicits_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___396_2470.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.mpreprocess =
                  (uu___396_2470.FStar_TypeChecker_Env.mpreprocess);
                FStar_TypeChecker_Env.postprocess =
                  (uu___396_2470.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___396_2470.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___396_2470.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___396_2470.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___396_2470.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (uu___396_2470.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (uu___396_2470.FStar_TypeChecker_Env.erasable_types_tab)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2496 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2496
               then
                 let uu____2499 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2502 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2499 uu____2502
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2536  ->
                         match uu____2536 with
                         | (b,uu____2546) ->
                             let t =
                               let uu____2552 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2552
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2555 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2556 -> []
                              | uu____2571 ->
                                  let uu____2572 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2572])))
                  in
               let as_lex_list dec =
                 let uu____2585 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2585 with
                 | (head,uu____2605) ->
                     (match head.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2633 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2641 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2650  ->
                         match uu___1_2650 with
                         | FStar_Syntax_Syntax.DECREASES uu____2652 -> true
                         | uu____2656 -> false))
                  in
               match uu____2641 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2663 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2684 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2713 =
              match uu____2713 with
              | (l,t,u_names) ->
                  let uu____2737 =
                    let uu____2738 = FStar_Syntax_Subst.compress t  in
                    uu____2738.FStar_Syntax_Syntax.n  in
                  (match uu____2737 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2797  ->
                                 match uu____2797 with
                                 | (x,imp) ->
                                     let uu____2816 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2816
                                     then
                                       let uu____2825 =
                                         let uu____2826 =
                                           let uu____2829 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2829
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2826
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2825, imp)
                                     else (x, imp)))
                          in
                       let uu____2836 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2836 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2857 =
                                let uu____2862 =
                                  let uu____2863 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2872 =
                                    let uu____2883 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2883]  in
                                  uu____2863 :: uu____2872  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2862
                                 in
                              uu____2857 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2918 = FStar_Util.prefix formals2  in
                            (match uu____2918 with
                             | (bs,(last,imp)) ->
                                 let last1 =
                                   let uu___463_2981 = last  in
                                   let uu____2982 =
                                     FStar_Syntax_Util.refine last precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___463_2981.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___463_2981.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2982
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last1, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____3018 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Medium
                                      in
                                   if uu____3018
                                   then
                                     let uu____3021 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____3023 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____3025 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____3021 uu____3023 uu____3025
                                   else ());
                                  (l, t', u_names))))
                   | uu____3032 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos)
               in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
  
let (wrap_guard_with_tactic_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun topt  ->
    fun g  ->
      match topt with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some tactic ->
          FStar_TypeChecker_Env.always_map_guard g
            (fun g1  ->
               let uu____3096 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____3096)
  
let (is_comp_ascribed_reflect :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____3119 =
      let uu____3120 = FStar_Syntax_Subst.compress e  in
      uu____3120.FStar_Syntax_Syntax.n  in
    match uu____3119 with
    | FStar_Syntax_Syntax.Tm_ascribed
        (e1,(FStar_Util.Inr uu____3132,uu____3133),uu____3134) ->
        let uu____3181 =
          let uu____3182 = FStar_Syntax_Subst.compress e1  in
          uu____3182.FStar_Syntax_Syntax.n  in
        (match uu____3181 with
         | FStar_Syntax_Syntax.Tm_app (head,args) when
             (FStar_List.length args) = Prims.int_one ->
             let uu____3229 =
               let uu____3230 = FStar_Syntax_Subst.compress head  in
               uu____3230.FStar_Syntax_Syntax.n  in
             (match uu____3229 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect l)
                  ->
                  let uu____3242 =
                    let uu____3249 = FStar_All.pipe_right args FStar_List.hd
                       in
                    FStar_All.pipe_right uu____3249
                      (fun uu____3305  ->
                         match uu____3305 with | (e2,aqual) -> (l, e2, aqual))
                     in
                  FStar_All.pipe_right uu____3242
                    (fun uu____3358  ->
                       FStar_Pervasives_Native.Some uu____3358)
              | uu____3359 -> FStar_Pervasives_Native.None)
         | uu____3366 -> FStar_Pervasives_Native.None)
    | uu____3373 -> FStar_Pervasives_Native.None
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____4098 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____4098
       then
         let uu____4101 =
           let uu____4103 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____4103  in
         let uu____4105 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1  in
         let uu____4107 = FStar_Syntax_Print.term_to_string e  in
         let uu____4109 =
           let uu____4111 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____4111  in
         let uu____4112 =
           let uu____4114 = FStar_TypeChecker_Env.expected_typ env  in
           match uu____4114 with
           | FStar_Pervasives_Native.None  -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t
            in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____4101 uu____4105 uu____4107 uu____4109 uu____4112
       else ());
      (let uu____4123 =
         FStar_Util.record_time
           (fun uu____4142  ->
              tc_maybe_toplevel_term
                (let uu___507_4145 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___507_4145.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___507_4145.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___507_4145.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___507_4145.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___507_4145.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___507_4145.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___507_4145.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___507_4145.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___507_4145.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___507_4145.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___507_4145.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___507_4145.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___507_4145.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___507_4145.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___507_4145.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___507_4145.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___507_4145.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___507_4145.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___507_4145.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___507_4145.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___507_4145.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___507_4145.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___507_4145.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___507_4145.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___507_4145.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___507_4145.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___507_4145.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___507_4145.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___507_4145.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___507_4145.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___507_4145.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___507_4145.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___507_4145.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___507_4145.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___507_4145.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___507_4145.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___507_4145.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___507_4145.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___507_4145.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___507_4145.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___507_4145.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___507_4145.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___507_4145.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___507_4145.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___507_4145.FStar_TypeChecker_Env.erasable_types_tab)
                 }) e)
          in
       match uu____4123 with
       | (r,ms) ->
           ((let uu____4170 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____4170
             then
               ((let uu____4174 =
                   let uu____4176 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____4176
                    in
                 let uu____4178 = FStar_Syntax_Print.term_to_string e  in
                 let uu____4180 =
                   let uu____4182 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____4182  in
                 let uu____4183 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____4174 uu____4178 uu____4180 uu____4183);
                (let uu____4186 = r  in
                 match uu____4186 with
                 | (e1,lc,uu____4195) ->
                     let uu____4196 =
                       let uu____4198 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____4198
                        in
                     let uu____4200 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____4202 =
                       FStar_TypeChecker_Common.lcomp_to_string lc  in
                     let uu____4204 =
                       let uu____4206 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____4206  in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____4196 uu____4200 uu____4202 uu____4204))
             else ());
            r))

and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      (let uu____4224 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____4224
       then
         let uu____4227 =
           let uu____4229 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____4229  in
         let uu____4231 = FStar_Syntax_Print.tag_of_term top  in
         let uu____4233 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____4227 uu____4231
           uu____4233
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4244 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____4266 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____4273 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____4286 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____4287 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____4288 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____4289 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____4290 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4309 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4324 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4331 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_4347 =
             match uu___2_4347 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4353 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name t =
               let uu____4369 =
                 let uu____4370 = FStar_Syntax_Subst.compress t  in
                 uu____4370.FStar_Syntax_Syntax.n  in
               match uu____4369 with
               | FStar_Syntax_Syntax.Tm_name uu____4374 -> true
               | uu____4376 -> false  in
             FStar_Util.for_some
               (fun uu____4386  ->
                  match uu____4386 with
                  | (uu____4392,t) ->
                      let uu____4394 = is_name t  in
                      Prims.op_Negation uu____4394)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____4413  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____4456  ->
                       match uu____4456 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___580_4485 = qi  in
                  let uu____4486 =
                    FStar_List.map
                      (fun uu____4514  ->
                         match uu____4514 with
                         | ((bv,uu____4530),bv') ->
                             let uu____4542 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____4542)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___580_4485.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4486
                  }  in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                let e1 =
                  FStar_List.fold_left
                    (fun t  ->
                       fun lb  ->
                         let uu____4554 =
                           let uu____4561 =
                             let uu____4562 =
                               let uu____4576 =
                                 let uu____4579 =
                                   let uu____4580 =
                                     let uu____4587 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____4587
                                      in
                                   [uu____4580]  in
                                 FStar_Syntax_Subst.close uu____4579 t  in
                               ((false, [lb]), uu____4576)  in
                             FStar_Syntax_Syntax.Tm_let uu____4562  in
                           FStar_Syntax_Syntax.mk uu____4561  in
                         uu____4554 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4623 =
                  FStar_List.fold_right
                    (fun uu____4659  ->
                       fun uu____4660  ->
                         match (uu____4659, uu____4660) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4729 = tc_term env_tm tm  in
                             (match uu____4729 with
                              | (tm1,uu____4747,g) ->
                                  let uu____4749 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4749))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4623 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___608_4791 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___608_4791.FStar_Syntax_Syntax.qkind);
                         FStar_Syntax_Syntax.antiquotes =
                           (FStar_List.rev aqs_rev)
                       }  in
                     let tm =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     value_check_expected_typ env1 tm
                       (FStar_Util.Inl FStar_Syntax_Syntax.t_term) guard)
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let c = FStar_Syntax_Syntax.mk_Tac FStar_Syntax_Syntax.t_term
                   in
                let uu____4802 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4802 with
                 | (env',uu____4816) ->
                     let uu____4821 =
                       tc_term
                         (let uu___617_4830 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___617_4830.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___617_4830.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___617_4830.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___617_4830.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___617_4830.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___617_4830.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___617_4830.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___617_4830.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___617_4830.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___617_4830.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___617_4830.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___617_4830.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___617_4830.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___617_4830.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___617_4830.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___617_4830.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___617_4830.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___617_4830.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___617_4830.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___617_4830.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___617_4830.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___617_4830.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___617_4830.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___617_4830.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___617_4830.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___617_4830.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___617_4830.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___617_4830.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___617_4830.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___617_4830.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___617_4830.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___617_4830.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___617_4830.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___617_4830.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___617_4830.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___617_4830.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___617_4830.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___617_4830.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___617_4830.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___617_4830.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___617_4830.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___617_4830.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___617_4830.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___617_4830.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___617_4830.FStar_TypeChecker_Env.erasable_types_tab)
                          }) qt
                        in
                     (match uu____4821 with
                      | (qt1,uu____4839,uu____4840) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4846 =
                            let uu____4853 =
                              let uu____4858 =
                                FStar_TypeChecker_Common.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4858  in
                            value_check_expected_typ env1 top uu____4853
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4846 with
                           | (t1,lc,g) ->
                               let t2 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (t1,
                                        (FStar_Syntax_Syntax.Meta_monadic_lift
                                           (FStar_Parser_Const.effect_PURE_lid,
                                             FStar_Parser_Const.effect_TAC_lid,
                                             FStar_Syntax_Syntax.t_term))))
                                   FStar_Pervasives_Native.None
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               (t2, lc, g)))))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____4875;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4876;
             FStar_Syntax_Syntax.ltyp = uu____4877;
             FStar_Syntax_Syntax.rng = uu____4878;_}
           ->
           let uu____4889 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4889
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4896 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4896 with
            | (e2,c,g) ->
                let g1 =
                  let uu___647_4913 = g  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___647_4913.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___647_4913.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___647_4913.FStar_TypeChecker_Common.implicits)
                  }  in
                let uu____4914 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4914, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names,pats)) ->
           let uu____4956 = FStar_Syntax_Util.type_u ()  in
           (match uu____4956 with
            | (t,u) ->
                let uu____4969 = tc_check_tot_or_gtot_term env1 e1 t ""  in
                (match uu____4969 with
                 | (e2,c,g) ->
                     let uu____4986 =
                       let uu____5003 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____5003 with
                       | (env2,uu____5027) -> tc_smt_pats env2 pats  in
                     (match uu____4986 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___670_5065 = g'  in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred =
                                (uu___670_5065.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___670_5065.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___670_5065.FStar_TypeChecker_Common.implicits)
                            }  in
                          let uu____5066 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____5085 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____5066, c, uu____5085))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____5091 =
             let uu____5092 = FStar_Syntax_Subst.compress e1  in
             uu____5092.FStar_Syntax_Syntax.n  in
           (match uu____5091 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____5101,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____5103;
                               FStar_Syntax_Syntax.lbtyp = uu____5104;
                               FStar_Syntax_Syntax.lbeff = uu____5105;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____5107;
                               FStar_Syntax_Syntax.lbpos = uu____5108;_}::[]),e2)
                ->
                let uu____5139 =
                  let uu____5146 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____5146 e11  in
                (match uu____5139 with
                 | (e12,c1,g1) ->
                     let uu____5156 = tc_term env1 e2  in
                     (match uu____5156 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2)
                             in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ
                             in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c2.FStar_TypeChecker_Common.res_typ
                             in
                          let attrs =
                            let uu____5180 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name
                               in
                            if uu____5180
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____5190 =
                              let uu____5197 =
                                let uu____5198 =
                                  let uu____5212 =
                                    let uu____5220 =
                                      let uu____5223 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_TypeChecker_Common.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____5223]  in
                                    (false, uu____5220)  in
                                  (uu____5212, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____5198  in
                              FStar_Syntax_Syntax.mk uu____5197  in
                            uu____5190 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.res_typ
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
                          let uu____5247 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____5247)))
            | uu____5248 ->
                let uu____5249 = tc_term env1 e1  in
                (match uu____5249 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____5271) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____5283) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____5302 = tc_term env1 e1  in
           (match uu____5302 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____5323,(FStar_Util.Inr expected_c,_tacopt),uu____5326) when
           let uu____5373 = FStar_All.pipe_right top is_comp_ascribed_reflect
              in
           FStar_All.pipe_right uu____5373 FStar_Util.is_some ->
           let uu____5405 =
             let uu____5416 =
               FStar_All.pipe_right top is_comp_ascribed_reflect  in
             FStar_All.pipe_right uu____5416 FStar_Util.must  in
           (match uu____5405 with
            | (effect_lid,e1,aqual) ->
                let uu____5490 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____5490 with
                 | (env0,uu____5504) ->
                     let uu____5509 = tc_comp env0 expected_c  in
                     (match uu____5509 with
                      | (expected_c1,uu____5523,g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1
                             in
                          ((let uu____5527 =
                              let uu____5529 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name
                                 in
                              Prims.op_Negation uu____5529  in
                            if uu____5527
                            then
                              let uu____5532 =
                                let uu____5538 =
                                  let uu____5540 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  let uu____5542 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5540 uu____5542
                                   in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5538)
                                 in
                              FStar_Errors.raise_error uu____5532
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5549 =
                              let uu____5551 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid
                                 in
                              Prims.op_Negation uu____5551  in
                            if uu____5549
                            then
                              let uu____5554 =
                                let uu____5560 =
                                  let uu____5562 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5562
                                   in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5560)
                                 in
                              FStar_Errors.raise_error uu____5554
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd
                               in
                            let repr =
                              let uu____5572 =
                                let uu____5575 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp
                                   in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5575 u_c
                                 in
                              FStar_All.pipe_right uu____5572 FStar_Util.must
                               in
                            let e2 =
                              let uu____5581 =
                                let uu____5588 =
                                  let uu____5589 =
                                    let uu____5616 =
                                      let uu____5633 =
                                        let uu____5642 =
                                          FStar_Syntax_Syntax.mk_Total' repr
                                            (FStar_Pervasives_Native.Some u_c)
                                           in
                                        FStar_Util.Inr uu____5642  in
                                      (uu____5633,
                                        FStar_Pervasives_Native.None)
                                       in
                                    (e1, uu____5616,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____5589
                                   in
                                FStar_Syntax_Syntax.mk uu____5588  in
                              uu____5581 FStar_Pervasives_Native.None
                                e1.FStar_Syntax_Syntax.pos
                               in
                            (let uu____5684 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme
                                in
                             if uu____5684
                             then
                               let uu____5688 =
                                 FStar_Syntax_Print.term_to_string e2  in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5688
                             else ());
                            (let uu____5693 = tc_tot_or_gtot_term env0 e2  in
                             match uu____5693 with
                             | (e3,uu____5707,g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3  in
                                 ((let uu____5711 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme
                                      in
                                   if uu____5711
                                   then
                                     let uu____5715 =
                                       FStar_Syntax_Print.term_to_string e4
                                        in
                                     let uu____5717 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e
                                        in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5715 uu____5717
                                   else ());
                                  (let top1 =
                                     let r = top.FStar_Syntax_Syntax.pos  in
                                     let tm =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_reflect
                                               effect_lid))
                                         FStar_Pervasives_Native.None r
                                        in
                                     let tm1 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (tm, [(e4, aqual)]))
                                         FStar_Pervasives_Native.None r
                                        in
                                     let uu____5764 =
                                       let uu____5771 =
                                         let uu____5772 =
                                           let uu____5799 =
                                             let uu____5802 =
                                               FStar_All.pipe_right
                                                 expected_c1
                                                 FStar_Syntax_Util.comp_effect_name
                                                in
                                             FStar_All.pipe_right uu____5802
                                               (fun uu____5807  ->
                                                  FStar_Pervasives_Native.Some
                                                    uu____5807)
                                              in
                                           (tm1,
                                             ((FStar_Util.Inr expected_c1),
                                               _tacopt), uu____5799)
                                            in
                                         FStar_Syntax_Syntax.Tm_ascribed
                                           uu____5772
                                          in
                                       FStar_Syntax_Syntax.mk uu____5771  in
                                     uu____5764 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let uu____5844 =
                                     let uu____5851 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     comp_check_expected_typ env1 top1
                                       uu____5851
                                      in
                                   match uu____5844 with
                                   | (top2,c,g_env) ->
                                       let uu____5861 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env]
                                          in
                                       (top2, c, uu____5861)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____5865) ->
           let uu____5912 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____5912 with
            | (env0,uu____5926) ->
                let uu____5931 = tc_comp env0 expected_c  in
                (match uu____5931 with
                 | (expected_c1,uu____5945,g) ->
                     let uu____5947 =
                       let uu____5954 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____5954 e1  in
                     (match uu____5947 with
                      | (e2,c',g') ->
                          let uu____5964 =
                            let uu____5975 =
                              FStar_TypeChecker_Common.lcomp_comp c'  in
                            match uu____5975 with
                            | (c'1,g_c') ->
                                let uu____5992 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1)
                                   in
                                (match uu____5992 with
                                 | (e3,expected_c2,g'') ->
                                     let uu____6012 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g''
                                        in
                                     (e3, expected_c2, uu____6012))
                             in
                          (match uu____5964 with
                           | (e3,expected_c2,g'') ->
                               let uu____6034 = tc_tactic_opt env0 topt  in
                               (match uu____6034 with
                                | (topt1,gtac) ->
                                    let e4 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_ascribed
                                           (e3,
                                             ((FStar_Util.Inr expected_c2),
                                               topt1),
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.comp_effect_name
                                                   expected_c2))))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let lc =
                                      FStar_TypeChecker_Common.lcomp_of_comp
                                        expected_c2
                                       in
                                    let f =
                                      let uu____6094 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____6094
                                       in
                                    let uu____6095 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____6095 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____6112 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____6112
                                            in
                                         let uu____6113 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____6113)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____6117) ->
           let uu____6164 = FStar_Syntax_Util.type_u ()  in
           (match uu____6164 with
            | (k,u) ->
                let uu____6177 = tc_check_tot_or_gtot_term env1 t k ""  in
                (match uu____6177 with
                 | (t1,uu____6192,f) ->
                     let uu____6194 = tc_tactic_opt env1 topt  in
                     (match uu____6194 with
                      | (topt1,gtac) ->
                          let uu____6213 =
                            let uu____6220 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____6220 e1  in
                          (match uu____6213 with
                           | (e2,c,g) ->
                               let uu____6230 =
                                 let uu____6235 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____6241  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____6235 e2 c f
                                  in
                               (match uu____6230 with
                                | (c1,f1) ->
                                    let uu____6251 =
                                      let uu____6258 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____6258
                                        c1
                                       in
                                    (match uu____6251 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____6305 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____6305
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____6307 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____6307)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6308;
              FStar_Syntax_Syntax.vars = uu____6309;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6388 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6388 with
            | (unary_op,uu____6412) ->
                let head =
                  let uu____6440 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6440
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6488;
              FStar_Syntax_Syntax.vars = uu____6489;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6568 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6568 with
            | (unary_op,uu____6592) ->
                let head =
                  let uu____6620 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6620
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6668);
              FStar_Syntax_Syntax.pos = uu____6669;
              FStar_Syntax_Syntax.vars = uu____6670;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6749 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6749 with
            | (unary_op,uu____6773) ->
                let head =
                  let uu____6801 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6801
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6849;
              FStar_Syntax_Syntax.vars = uu____6850;_},a1::a2::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6946 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6946 with
            | (unary_op,uu____6970) ->
                let head =
                  let uu____6998 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____6998
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____7054;
              FStar_Syntax_Syntax.vars = uu____7055;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____7093 =
             let uu____7100 =
               let uu____7101 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7101  in
             tc_term uu____7100 e1  in
           (match uu____7093 with
            | (e2,c,g) ->
                let uu____7125 = FStar_Syntax_Util.head_and_args top  in
                (match uu____7125 with
                 | (head,uu____7149) ->
                     let uu____7174 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____7207 =
                       let uu____7208 =
                         let uu____7209 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____7209  in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7208
                        in
                     (uu____7174, uu____7207, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7210;
              FStar_Syntax_Syntax.vars = uu____7211;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____7264 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7264 with
            | (head,uu____7288) ->
                let env' =
                  let uu____7314 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____7314  in
                let uu____7315 = tc_term env' r  in
                (match uu____7315 with
                 | (er,uu____7329,gr) ->
                     let uu____7331 = tc_term env1 t  in
                     (match uu____7331 with
                      | (t1,tt,gt) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt  in
                          let uu____7348 =
                            let uu____7349 =
                              let uu____7354 =
                                let uu____7355 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____7364 =
                                  let uu____7375 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____7375]  in
                                uu____7355 :: uu____7364  in
                              FStar_Syntax_Syntax.mk_Tm_app head uu____7354
                               in
                            uu____7349 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____7348, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____7408;
              FStar_Syntax_Syntax.vars = uu____7409;_},uu____7410)
           ->
           let uu____7435 =
             let uu____7441 =
               let uu____7443 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7443  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7441)  in
           FStar_Errors.raise_error uu____7435 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7453;
              FStar_Syntax_Syntax.vars = uu____7454;_},uu____7455)
           ->
           let uu____7480 =
             let uu____7486 =
               let uu____7488 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7488  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7486)  in
           FStar_Errors.raise_error uu____7480 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____7498;
              FStar_Syntax_Syntax.vars = uu____7499;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7546 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____7546 with
             | (env0,uu____7560) ->
                 let uu____7565 = tc_term env0 e1  in
                 (match uu____7565 with
                  | (e2,c,g) ->
                      let uu____7581 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____7581 with
                       | (reify_op,uu____7605) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____7631 =
                             FStar_TypeChecker_Common.lcomp_comp c  in
                           (match uu____7631 with
                            | (c1,g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1  in
                                ((let uu____7646 =
                                    let uu____7648 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef
                                       in
                                    Prims.op_Negation uu____7648  in
                                  if uu____7646
                                  then
                                    let uu____7651 =
                                      let uu____7657 =
                                        let uu____7659 =
                                          FStar_Ident.string_of_lid ef  in
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          uu____7659
                                         in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7657)
                                       in
                                    FStar_Errors.raise_error uu____7651
                                      e2.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let repr =
                                    FStar_TypeChecker_Env.reify_comp env1 c1
                                      u_c
                                     in
                                  let e3 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (reify_op, [(e2, aqual)]))
                                      FStar_Pervasives_Native.None
                                      top.FStar_Syntax_Syntax.pos
                                     in
                                  let c2 =
                                    let uu____7702 =
                                      (FStar_TypeChecker_Env.is_total_effect
                                         env1 ef)
                                        ||
                                        (let uu____7705 =
                                           FStar_All.pipe_right ef
                                             (FStar_TypeChecker_Env.norm_eff_name
                                                env1)
                                            in
                                         FStar_All.pipe_right uu____7705
                                           (FStar_TypeChecker_Env.is_layered_effect
                                              env1))
                                       in
                                    if uu____7702
                                    then
                                      let uu____7708 =
                                        FStar_Syntax_Syntax.mk_Total repr  in
                                      FStar_All.pipe_right uu____7708
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                    else
                                      (let ct =
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_c];
                                           FStar_Syntax_Syntax.effect_name =
                                             FStar_Parser_Const.effect_Dv_lid;
                                           FStar_Syntax_Syntax.result_typ =
                                             repr;
                                           FStar_Syntax_Syntax.effect_args =
                                             [];
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       let uu____7720 =
                                         FStar_Syntax_Syntax.mk_Comp ct  in
                                       FStar_All.pipe_right uu____7720
                                         FStar_TypeChecker_Common.lcomp_of_comp)
                                     in
                                  let uu____7721 =
                                    comp_check_expected_typ env1 e3 c2  in
                                  match uu____7721 with
                                  | (e4,c3,g') ->
                                      let uu____7737 =
                                        let uu____7738 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g'
                                           in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7738
                                         in
                                      (e4, c3, uu____7737))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7740;
              FStar_Syntax_Syntax.vars = uu____7741;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7789 =
               let uu____7791 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l  in
               Prims.op_Negation uu____7791  in
             if uu____7789
             then
               let uu____7794 =
                 let uu____7800 =
                   let uu____7802 = FStar_Ident.string_of_lid l  in
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     uu____7802
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7800)  in
               FStar_Errors.raise_error uu____7794 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7808 = FStar_Syntax_Util.head_and_args top  in
             match uu____7808 with
             | (reflect_op,uu____7832) ->
                 let uu____7857 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____7857 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____7878 =
                        let uu____7884 =
                          let uu____7886 = FStar_Ident.string_of_lid l  in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7886
                           in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7884)  in
                      FStar_Errors.raise_error uu____7878
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____7908 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____7908 with
                       | (env_no_ex,uu____7922) ->
                           let uu____7927 =
                             let uu____7936 =
                               tc_tot_or_gtot_term env_no_ex e1  in
                             match uu____7936 with
                             | (e2,c,g) ->
                                 ((let uu____7955 =
                                     let uu____7957 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c
                                        in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7957
                                      in
                                   if uu____7955
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g))
                              in
                           (match uu____7927 with
                            | (e2,c_e,g_e) ->
                                let uu____7995 =
                                  let uu____8010 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____8010 with
                                  | (a,u_a) ->
                                      let uu____8031 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a
                                         in
                                      (match uu____8031 with
                                       | (a_uvar,uu____8060,g_a) ->
                                           let uu____8074 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar
                                              in
                                           (uu____8074, u_a, a_uvar, g_a))
                                   in
                                (match uu____7995 with
                                 | ((expected_repr_typ,g_repr),u_a,a,g_a) ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ
                                        in
                                     let eff_args =
                                       let uu____8116 =
                                         let uu____8117 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ
                                            in
                                         uu____8117.FStar_Syntax_Syntax.n  in
                                       match uu____8116 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8130,uu____8131::args) ->
                                           args
                                       | uu____8173 ->
                                           let uu____8174 =
                                             let uu____8180 =
                                               let uu____8182 =
                                                 FStar_Ident.string_of_lid l
                                                  in
                                               let uu____8184 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ
                                                  in
                                               let uu____8186 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ
                                                  in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____8182 uu____8184
                                                 uu____8186
                                                in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____8180)
                                              in
                                           FStar_Errors.raise_error
                                             uu____8174
                                             top.FStar_Syntax_Syntax.pos
                                        in
                                     let c =
                                       let uu____8201 =
                                         FStar_Syntax_Syntax.mk_Comp
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               [u_a];
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               a;
                                             FStar_Syntax_Syntax.effect_args
                                               = eff_args;
                                             FStar_Syntax_Syntax.flags = []
                                           }
                                          in
                                       FStar_All.pipe_right uu____8201
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____8237 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____8237 with
                                      | (e4,c1,g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_TypeChecker_Common.eff_name),
                                                        (c1.FStar_TypeChecker_Common.res_typ)))))
                                              FStar_Pervasives_Native.None
                                              e4.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____8260 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g']
                                             in
                                          (e5, c1, uu____8260))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8299 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8299 with
            | (head1,args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head,(uu____8349,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____8350))::(tau,FStar_Pervasives_Native.None
                                                               )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8403 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8403 with
            | (head1,args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8478 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8688 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____8478 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let env0 = env1  in
           let env2 =
             let uu____8807 =
               let uu____8808 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____8808 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____8807 instantiate_both  in
           ((let uu____8824 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____8824
             then
               let uu____8827 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____8829 = FStar_Syntax_Print.term_to_string top  in
               let uu____8831 =
                 let uu____8833 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____8833
                   (fun uu___3_8840  ->
                      match uu___3_8840 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8827
                 uu____8829 uu____8831
             else ());
            (let uu____8849 = tc_term (no_inst env2) head  in
             match uu____8849 with
             | (head1,chead,g_head) ->
                 let uu____8865 =
                   let uu____8870 = FStar_TypeChecker_Common.lcomp_comp chead
                      in
                   FStar_All.pipe_right uu____8870
                     (fun uu____8887  ->
                        match uu____8887 with
                        | (c,g) ->
                            let uu____8898 =
                              FStar_TypeChecker_Env.conj_guard g_head g  in
                            (c, uu____8898))
                    in
                 (match uu____8865 with
                  | (chead1,g_head1) ->
                      let uu____8907 =
                        let uu____8914 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8917 = FStar_Options.lax ()  in
                              Prims.op_Negation uu____8917))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head1)
                           in
                        if uu____8914
                        then
                          let uu____8926 =
                            let uu____8933 =
                              FStar_TypeChecker_Env.expected_typ env0  in
                            check_short_circuit_args env2 head1 chead1
                              g_head1 args uu____8933
                             in
                          match uu____8926 with | (e1,c,g) -> (e1, c, g)
                        else
                          (let uu____8947 =
                             FStar_TypeChecker_Env.expected_typ env0  in
                           check_application_args env2 head1 chead1 g_head1
                             args uu____8947)
                         in
                      (match uu____8907 with
                       | (e1,c,g) ->
                           let uu____8959 =
                             let uu____8966 =
                               let uu____8968 =
                                 let uu____8969 =
                                   let uu____8970 =
                                     FStar_TypeChecker_Common.lcomp_comp c
                                      in
                                   FStar_All.pipe_right uu____8970
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_TypeChecker_Common.lcomp_of_comp
                                   uu____8969
                                  in
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 uu____8968
                                in
                             if uu____8966
                             then
                               let uu____8986 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ
                                  in
                               match uu____8986 with
                               | (e2,res_typ,implicits) ->
                                   let uu____9002 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ
                                      in
                                   (e2, uu____9002, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard)
                              in
                           (match uu____8959 with
                            | (e2,c1,implicits) ->
                                ((let uu____9015 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme
                                     in
                                  if uu____9015
                                  then
                                    let uu____9018 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g
                                       in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____9018
                                  else ());
                                 (let uu____9023 =
                                    comp_check_expected_typ env0 e2 c1  in
                                  match uu____9023 with
                                  | (e3,c2,g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits
                                         in
                                      ((let uu____9042 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme
                                           in
                                        if uu____9042
                                        then
                                          let uu____9045 =
                                            FStar_Syntax_Print.term_to_string
                                              e3
                                             in
                                          let uu____9047 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1
                                             in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____9045 uu____9047
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____9052 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9075;
                FStar_Syntax_Syntax.lbunivs = uu____9076;
                FStar_Syntax_Syntax.lbtyp = uu____9077;
                FStar_Syntax_Syntax.lbeff = uu____9078;
                FStar_Syntax_Syntax.lbdef = uu____9079;
                FStar_Syntax_Syntax.lbattrs = uu____9080;
                FStar_Syntax_Syntax.lbpos = uu____9081;_}::[]),uu____9082)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____9108),uu____9109) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9127;
                FStar_Syntax_Syntax.lbunivs = uu____9128;
                FStar_Syntax_Syntax.lbtyp = uu____9129;
                FStar_Syntax_Syntax.lbeff = uu____9130;
                FStar_Syntax_Syntax.lbdef = uu____9131;
                FStar_Syntax_Syntax.lbattrs = uu____9132;
                FStar_Syntax_Syntax.lbpos = uu____9133;_}::uu____9134),uu____9135)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____9163),uu____9164) ->
           check_inner_let_rec env1 top)

and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let uu____9190 =
        let uu____9191 = FStar_Syntax_Subst.compress top  in
        uu____9191.FStar_Syntax_Syntax.n  in
      match uu____9190 with
      | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
          let uu____9238 = FStar_TypeChecker_Env.clear_expected_typ env  in
          (match uu____9238 with
           | (env1,topt) ->
               let env11 = instantiate_both env1  in
               let uu____9258 = tc_term env11 e1  in
               (match uu____9258 with
                | (e11,c1,g1) ->
                    let uu____9274 =
                      let uu____9285 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1  in
                      match uu____9285 with
                      | FStar_Pervasives_Native.Some (e12,c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None  -> (e11, c1, eqns)  in
                    (match uu____9274 with
                     | (e12,c11,eqns1) ->
                         let eqns2 = eqns1  in
                         let uu____9340 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None  ->
                               let uu____9354 = FStar_Syntax_Util.type_u ()
                                  in
                               (match uu____9354 with
                                | (k,uu____9366) ->
                                    let uu____9367 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k
                                       in
                                    (match uu____9367 with
                                     | (res_t,uu____9388,g) ->
                                         let uu____9402 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t
                                            in
                                         let uu____9403 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g
                                            in
                                         (uu____9402, res_t, uu____9403)))
                            in
                         (match uu____9340 with
                          | (env_branches,res_t,g11) ->
                              ((let uu____9414 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme
                                   in
                                if uu____9414
                                then
                                  let uu____9417 =
                                    FStar_Syntax_Print.term_to_string res_t
                                     in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____9417
                                else ());
                               (let guard_x =
                                  FStar_Syntax_Syntax.new_bv
                                    (FStar_Pervasives_Native.Some
                                       (e12.FStar_Syntax_Syntax.pos))
                                    c11.FStar_TypeChecker_Common.res_typ
                                   in
                                let t_eqns =
                                  FStar_All.pipe_right eqns2
                                    (FStar_List.map
                                       (tc_eqn guard_x env_branches))
                                   in
                                let uu____9525 =
                                  let uu____9533 =
                                    FStar_List.fold_right
                                      (fun uu____9626  ->
                                         fun uu____9627  ->
                                           match (uu____9626, uu____9627)
                                           with
                                           | ((branch,f,eff_label,cflags,c,g,erasable_branch),
                                              (caccum,gaccum,erasable)) ->
                                               let uu____9899 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum
                                                  in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9899,
                                                 (erasable || erasable_branch)))
                                      t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false)
                                     in
                                  match uu____9533 with
                                  | (cases,g,erasable) ->
                                      let uu____10013 =
                                        FStar_TypeChecker_Util.bind_cases env
                                          res_t cases guard_x
                                         in
                                      (uu____10013, g, erasable)
                                   in
                                match uu____9525 with
                                | (c_branches,g_branches,erasable) ->
                                    let cres =
                                      FStar_TypeChecker_Util.bind
                                        e12.FStar_Syntax_Syntax.pos env
                                        (FStar_Pervasives_Native.Some e12)
                                        c11
                                        ((FStar_Pervasives_Native.Some
                                            guard_x), c_branches)
                                       in
                                    let cres1 =
                                      if erasable
                                      then
                                        let e =
                                          FStar_Syntax_Util.exp_true_bool  in
                                        let c =
                                          FStar_Syntax_Syntax.mk_GTotal'
                                            FStar_Syntax_Util.t_bool
                                            (FStar_Pervasives_Native.Some
                                               FStar_Syntax_Syntax.U_zero)
                                           in
                                        let uu____10033 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c
                                           in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____10033
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres  in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____10175  ->
                                                  match uu____10175 with
                                                  | ((pat,wopt,br),uu____10223,eff_label,uu____10225,uu____10226,uu____10227,uu____10228)
                                                      ->
                                                      let uu____10267 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t
                                                         in
                                                      (pat, wopt,
                                                        uu____10267)))
                                           in
                                        let e =
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_match
                                               (scrutinee, branches))
                                            FStar_Pervasives_Native.None
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let e2 =
                                          FStar_TypeChecker_Util.maybe_monadic
                                            env e
                                            cres1.FStar_TypeChecker_Common.eff_name
                                            cres1.FStar_TypeChecker_Common.res_typ
                                           in
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl
                                                   (cres1.FStar_TypeChecker_Common.res_typ)),
                                                 FStar_Pervasives_Native.None),
                                               (FStar_Pervasives_Native.Some
                                                  (cres1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          e2.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____10334 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name
                                         in
                                      if uu____10334
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____10342 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x
                                              in
                                           mk_match uu____10342  in
                                         let lb =
                                           let uu____10346 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name
                                              in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____10346 e12 []
                                             e12.FStar_Syntax_Syntax.pos
                                            in
                                         let e =
                                           let uu____10352 =
                                             let uu____10359 =
                                               let uu____10360 =
                                                 let uu____10374 =
                                                   let uu____10377 =
                                                     let uu____10378 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         guard_x
                                                        in
                                                     [uu____10378]  in
                                                   FStar_Syntax_Subst.close
                                                     uu____10377 e_match
                                                    in
                                                 ((false, [lb]), uu____10374)
                                                  in
                                               FStar_Syntax_Syntax.Tm_let
                                                 uu____10360
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10359
                                              in
                                           uu____10352
                                             FStar_Pervasives_Native.None
                                             top.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ)
                                       in
                                    ((let uu____10411 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme
                                         in
                                      if uu____10411
                                      then
                                        let uu____10414 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let uu____10416 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1
                                           in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____10414 uu____10416
                                      else ());
                                     (let uu____10421 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches
                                         in
                                      (e, cres1, uu____10421)))))))))
      | uu____10422 ->
          let uu____10423 =
            let uu____10425 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format1 "tc_match called on %s\n" uu____10425  in
          failwith uu____10423

and (tc_synth :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun head  ->
    fun env  ->
      fun args  ->
        fun rng  ->
          let uu____10450 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____10489))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____10530 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____10450 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____10563 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____10563 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____10567 =
                           FStar_TypeChecker_Env.get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____10567)
                 in
              let uu____10570 =
                let uu____10577 =
                  let uu____10578 =
                    let uu____10579 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____10579
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____10578  in
                tc_term uu____10577 typ  in
              (match uu____10570 with
               | (typ1,uu____10595,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____10598 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau
                        in
                     match uu____10598 with
                     | (tau1,uu____10612,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1347_10617 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1347_10617.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1347_10617.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____10619 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____10619
                            then
                              let uu____10624 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____10624
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10630 =
                              let uu____10631 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10631
                               in
                            (t, uu____10630,
                              FStar_TypeChecker_Env.trivial_guard)))))))

and (tc_tactic :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun a  ->
    fun b  ->
      fun env  ->
        fun tau  ->
          let env1 =
            let uu___1357_10637 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1357_10637.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1357_10637.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1357_10637.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1357_10637.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1357_10637.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1357_10637.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1357_10637.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1357_10637.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1357_10637.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1357_10637.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1357_10637.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1357_10637.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1357_10637.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1357_10637.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1357_10637.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1357_10637.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1357_10637.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1357_10637.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1357_10637.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1357_10637.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1357_10637.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1357_10637.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1357_10637.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1357_10637.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1357_10637.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1357_10637.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1357_10637.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1357_10637.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1357_10637.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1357_10637.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1357_10637.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1357_10637.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1357_10637.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1357_10637.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1357_10637.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1357_10637.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1357_10637.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1357_10637.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1357_10637.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1357_10637.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1357_10637.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1357_10637.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1357_10637.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1357_10637.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1357_10637.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____10639 = FStar_Syntax_Syntax.t_tac_of a b  in
          tc_check_tot_or_gtot_term env1 tau uu____10639 ""

and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____10662 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic
             in
          (match uu____10662 with
           | (tactic1,uu____10676,g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))

and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v dc e1 t0 =
        let t = FStar_Syntax_Util.remove_inacc t0  in
        let uu____10729 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____10729 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____10750 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____10750
              then FStar_Util.Inl t1
              else
                (let uu____10759 =
                   let uu____10760 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____10760
                    in
                 FStar_Util.Inr uu____10759)
               in
            let is_data_ctor uu___4_10769 =
              match uu___4_10769 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10774) -> true
              | uu____10782 -> false  in
            let uu____10786 =
              (is_data_ctor dc) &&
                (let uu____10789 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____10789)
               in
            if uu____10786
            then
              let uu____10798 =
                let uu____10804 =
                  let uu____10806 =
                    FStar_Ident.string_of_lid v.FStar_Syntax_Syntax.v  in
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    uu____10806
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10804)  in
              let uu____10810 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____10798 uu____10810
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10828 =
            let uu____10834 =
              let uu____10836 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10836
               in
            (FStar_Errors.Error_IllScopedTerm, uu____10834)  in
          FStar_Errors.raise_error uu____10828 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____10864 =
            let uu____10869 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____10869  in
          value_check_expected_typ env1 e uu____10864
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____10871 =
            let uu____10884 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____10884 with
            | FStar_Pervasives_Native.None  ->
                let uu____10899 = FStar_Syntax_Util.type_u ()  in
                (match uu____10899 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____10871 with
           | (t,uu____10937,g0) ->
               let uu____10951 =
                 let uu____10964 =
                   let uu____10966 = FStar_Range.string_of_range r  in
                   Prims.op_Hat "user-provided implicit term at " uu____10966
                    in
                 FStar_TypeChecker_Util.new_implicit_var uu____10964 r env1 t
                  in
               (match uu____10951 with
                | (e1,uu____10976,g1) ->
                    let uu____10990 =
                      let uu____10991 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____10991
                        FStar_TypeChecker_Common.lcomp_of_comp
                       in
                    let uu____10992 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____10990, uu____10992)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10994 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____11004 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____11004)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____10994 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1423_11018 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1423_11018.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1423_11018.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____11021 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____11021 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____11042 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____11042
                       then FStar_Util.Inl t1
                       else
                         (let uu____11051 =
                            let uu____11052 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____11052
                             in
                          FStar_Util.Inr uu____11051)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____11054;
             FStar_Syntax_Syntax.vars = uu____11055;_},uu____11056)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____11061 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____11061
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____11071 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____11071
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____11081;
             FStar_Syntax_Syntax.vars = uu____11082;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____11091 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____11091 with
           | ((us',t),range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range  in
               (maybe_warn_on_use env1 fv1;
                if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____11117 =
                     let uu____11123 =
                       let uu____11125 = FStar_Syntax_Print.fv_to_string fv1
                          in
                       let uu____11127 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____11129 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____11125 uu____11127 uu____11129
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____11123)
                      in
                   let uu____11133 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____11117 uu____11133)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____11152 -> failwith "Impossible") us' us1;
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____11156 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____11156 us1  in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_uinst (uu____11157,us) ->
          let uu____11163 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
              "Universe applications are only allowed on top-level identifiers")
            uu____11163
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____11173 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____11173 with
           | ((us,t),range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range  in
               (maybe_warn_on_use env1 fv1;
                (let uu____11198 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____11198
                 then
                   let uu____11203 =
                     let uu____11205 = FStar_Syntax_Syntax.lid_of_fv fv1  in
                     FStar_Syntax_Print.lid_to_string uu____11205  in
                   let uu____11206 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____11208 = FStar_Range.string_of_range range  in
                   let uu____11210 = FStar_Range.string_of_use_range range
                      in
                   let uu____11212 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____11203 uu____11206 uu____11208 uu____11210
                     uu____11212
                 else ());
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____11219 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____11219 us  in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____11247 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____11247 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____11261 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11261 with
                | (env2,uu____11275) ->
                    let uu____11280 = tc_binders env2 bs1  in
                    (match uu____11280 with
                     | (bs2,env3,g,us) ->
                         let uu____11299 = tc_comp env3 c1  in
                         (match uu____11299 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1509_11318 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1509_11318.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1509_11318.FStar_Syntax_Syntax.vars)
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
                                  let uu____11329 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____11329
                                   in
                                let g2 =
                                  FStar_TypeChecker_Util.close_guard_implicits
                                    env3 false bs2 g1
                                   in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g2))))))
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
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____11346 =
            let uu____11351 =
              let uu____11352 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11352]  in
            FStar_Syntax_Subst.open_term uu____11351 phi  in
          (match uu____11346 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____11380 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11380 with
                | (env2,uu____11394) ->
                    let uu____11399 =
                      let uu____11414 = FStar_List.hd x1  in
                      tc_binder env2 uu____11414  in
                    (match uu____11399 with
                     | (x2,env3,f1,u) ->
                         ((let uu____11450 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____11450
                           then
                             let uu____11453 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____11455 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11457 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____11453 uu____11455 uu____11457
                           else ());
                          (let uu____11464 = FStar_Syntax_Util.type_u ()  in
                           match uu____11464 with
                           | (t_phi,uu____11476) ->
                               let uu____11477 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                   "refinement formula must be pure or ghost"
                                  in
                               (match uu____11477 with
                                | (phi2,uu____11492,f2) ->
                                    let e1 =
                                      let uu___1547_11497 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1547_11497.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1547_11497.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____11506 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____11506
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____11535) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____11562 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____11562
            then
              let uu____11565 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1560_11569 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1560_11569.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1560_11569.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____11565
            else ());
           (let uu____11585 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____11585 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____11598 ->
          let uu____11599 =
            let uu____11601 = FStar_Syntax_Print.term_to_string top  in
            let uu____11603 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____11601
              uu____11603
             in
          failwith uu____11599

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        let res =
          match c with
          | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
          | FStar_Const.Const_bool uu____11616 -> FStar_Syntax_Util.t_bool
          | FStar_Const.Const_int (uu____11618,FStar_Pervasives_Native.None )
              -> FStar_Syntax_Syntax.t_int
          | FStar_Const.Const_int
              (uu____11631,FStar_Pervasives_Native.Some msize) ->
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
          | FStar_Const.Const_string uu____11649 ->
              FStar_Syntax_Syntax.t_string
          | FStar_Const.Const_real uu____11655 -> FStar_Syntax_Syntax.t_real
          | FStar_Const.Const_float uu____11657 ->
              FStar_Syntax_Syntax.t_float
          | FStar_Const.Const_char uu____11658 ->
              let uu____11660 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____11660 FStar_Util.must
          | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
          | FStar_Const.Const_range uu____11665 ->
              FStar_Syntax_Syntax.t_range
          | FStar_Const.Const_range_of  ->
              let uu____11666 =
                let uu____11672 =
                  let uu____11674 = FStar_Parser_Const.const_to_string c  in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11674
                   in
                (FStar_Errors.Fatal_IllTyped, uu____11672)  in
              FStar_Errors.raise_error uu____11666 r
          | FStar_Const.Const_set_range_of  ->
              let uu____11678 =
                let uu____11684 =
                  let uu____11686 = FStar_Parser_Const.const_to_string c  in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11686
                   in
                (FStar_Errors.Fatal_IllTyped, uu____11684)  in
              FStar_Errors.raise_error uu____11678 r
          | FStar_Const.Const_reify  ->
              let uu____11690 =
                let uu____11696 =
                  let uu____11698 = FStar_Parser_Const.const_to_string c  in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11698
                   in
                (FStar_Errors.Fatal_IllTyped, uu____11696)  in
              FStar_Errors.raise_error uu____11690 r
          | FStar_Const.Const_reflect uu____11702 ->
              let uu____11703 =
                let uu____11709 =
                  let uu____11711 = FStar_Parser_Const.const_to_string c  in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11711
                   in
                (FStar_Errors.Fatal_IllTyped, uu____11709)  in
              FStar_Errors.raise_error uu____11703 r
          | uu____11715 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnsupportedConstant,
                  "Unsupported constant") r
           in
        FStar_Syntax_Subst.set_use_range r res

and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      let c0 = c  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____11734) ->
          let uu____11743 = FStar_Syntax_Util.type_u ()  in
          (match uu____11743 with
           | (k,u) ->
               let uu____11756 = tc_check_tot_or_gtot_term env t k ""  in
               (match uu____11756 with
                | (t1,uu____11771,g) ->
                    let uu____11773 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11773, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____11775) ->
          let uu____11784 = FStar_Syntax_Util.type_u ()  in
          (match uu____11784 with
           | (k,u) ->
               let uu____11797 = tc_check_tot_or_gtot_term env t k ""  in
               (match uu____11797 with
                | (t1,uu____11812,g) ->
                    let uu____11814 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11814, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          let head1 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____11824 =
              let uu____11829 =
                let uu____11830 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____11830 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head1 uu____11829  in
            uu____11824 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____11847 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff ""  in
          (match uu____11847 with
           | (tc1,uu____11862,f) ->
               let uu____11864 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____11864 with
                | (head2,args) ->
                    let comp_univs =
                      let uu____11914 =
                        let uu____11915 = FStar_Syntax_Subst.compress head2
                           in
                        uu____11915.FStar_Syntax_Syntax.n  in
                      match uu____11914 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11918,us) -> us
                      | uu____11924 -> []  in
                    let uu____11925 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____11925 with
                     | (uu____11948,args1) ->
                         let uu____11974 =
                           let uu____11997 = FStar_List.hd args1  in
                           let uu____12014 = FStar_List.tl args1  in
                           (uu____11997, uu____12014)  in
                         (match uu____11974 with
                          | (res,args2) ->
                              let uu____12095 =
                                let uu____12104 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_12132  ->
                                          match uu___5_12132 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____12140 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____12140 with
                                               | (env1,uu____12152) ->
                                                   let uu____12157 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____12157 with
                                                    | (e1,uu____12169,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____12104
                                  FStar_List.unzip
                                 in
                              (match uu____12095 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1690_12210 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1690_12210.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags = flags
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____12216 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____12216))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____12226 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____12230 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____12242 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____12242
        | FStar_Syntax_Syntax.U_max us ->
            let uu____12246 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____12246
        | FStar_Syntax_Syntax.U_name x ->
            let uu____12250 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____12250
            then u2
            else
              (let uu____12255 =
                 let uu____12257 =
                   let uu____12259 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____12259 " not found"  in
                 Prims.op_Hat "Universe variable " uu____12257  in
               failwith uu____12255)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____12266 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____12266 FStar_Pervasives_Native.snd
         | uu____12275 -> aux u)

and (tc_abs_expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
            FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders *
            FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option *
            FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun bs  ->
      fun t0  ->
        fun body  ->
          match t0 with
          | FStar_Pervasives_Native.None  ->
              ((match env.FStar_TypeChecker_Env.letrecs with
                | [] -> ()
                | uu____12307 ->
                    failwith
                      "Impossible: Can't have a let rec annotation but no expected type");
               (let uu____12317 = tc_binders env bs  in
                match uu____12317 with
                | (bs1,envbody,g_env,uu____12347) ->
                    (FStar_Pervasives_Native.None, bs1, [],
                      FStar_Pervasives_Native.None, envbody, body, g_env)))
          | FStar_Pervasives_Native.Some t ->
              let t1 = FStar_Syntax_Subst.compress t  in
              let rec as_function_typ norm1 t2 =
                let uu____12393 =
                  let uu____12394 = FStar_Syntax_Subst.compress t2  in
                  uu____12394.FStar_Syntax_Syntax.n  in
                match uu____12393 with
                | FStar_Syntax_Syntax.Tm_uvar uu____12417 ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____12437 -> failwith "Impossible");
                     (let uu____12447 = tc_binders env bs  in
                      match uu____12447 with
                      | (bs1,envbody,g_env,uu____12479) ->
                          let uu____12480 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody
                             in
                          (match uu____12480 with
                           | (envbody1,uu____12508) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12519;
                       FStar_Syntax_Syntax.pos = uu____12520;
                       FStar_Syntax_Syntax.vars = uu____12521;_},uu____12522)
                    ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____12566 -> failwith "Impossible");
                     (let uu____12576 = tc_binders env bs  in
                      match uu____12576 with
                      | (bs1,envbody,g_env,uu____12608) ->
                          let uu____12609 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody
                             in
                          (match uu____12609 with
                           | (envbody1,uu____12637) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_refine (b,uu____12649) ->
                    let uu____12654 =
                      as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                    (match uu____12654 with
                     | (uu____12695,bs1,bs',copt,env_body,body1,g_env) ->
                         ((FStar_Pervasives_Native.Some t2), bs1, bs', copt,
                           env_body, body1, g_env))
                | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                    let uu____12742 =
                      FStar_Syntax_Subst.open_comp bs_expected c_expected  in
                    (match uu____12742 with
                     | (bs_expected1,c_expected1) ->
                         let check_actuals_against_formals env1 bs1
                           bs_expected2 body1 =
                           let rec handle_more uu____12877 c_expected2 body2
                             =
                             match uu____12877 with
                             | (env_bs,bs2,more,guard_env,subst) ->
                                 (match more with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____12991 =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2
                                         in
                                      (env_bs, bs2, guard_env, uu____12991,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inr more_bs_expected) ->
                                      let c =
                                        let uu____13008 =
                                          FStar_Syntax_Util.arrow
                                            more_bs_expected c_expected2
                                           in
                                        FStar_Syntax_Syntax.mk_Total
                                          uu____13008
                                         in
                                      let uu____13009 =
                                        FStar_Syntax_Subst.subst_comp subst c
                                         in
                                      (env_bs, bs2, guard_env, uu____13009,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inl more_bs) ->
                                      let c =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2
                                         in
                                      let uu____13026 =
                                        (FStar_Options.ml_ish ()) ||
                                          (FStar_Syntax_Util.is_named_tot c)
                                         in
                                      if uu____13026
                                      then
                                        let t3 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env_bs
                                            (FStar_Syntax_Util.comp_result c)
                                           in
                                        (match t3.FStar_Syntax_Syntax.n with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs_expected3,c_expected3) ->
                                             let uu____13092 =
                                               FStar_Syntax_Subst.open_comp
                                                 bs_expected3 c_expected3
                                                in
                                             (match uu____13092 with
                                              | (bs_expected4,c_expected4) ->
                                                  let uu____13119 =
                                                    tc_abs_check_binders
                                                      env_bs more_bs
                                                      bs_expected4
                                                     in
                                                  (match uu____13119 with
                                                   | (env_bs_bs',bs',more1,guard'_env_bs,subst1)
                                                       ->
                                                       let guard'_env =
                                                         FStar_TypeChecker_Env.close_guard
                                                           env_bs bs2
                                                           guard'_env_bs
                                                          in
                                                       let uu____13174 =
                                                         let uu____13201 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard_env
                                                             guard'_env
                                                            in
                                                         (env_bs_bs',
                                                           (FStar_List.append
                                                              bs2 bs'),
                                                           more1,
                                                           uu____13201,
                                                           subst1)
                                                          in
                                                       handle_more
                                                         uu____13174
                                                         c_expected4 body2))
                                         | uu____13224 ->
                                             let body3 =
                                               FStar_Syntax_Util.abs more_bs
                                                 body2
                                                 FStar_Pervasives_Native.None
                                                in
                                             (env_bs, bs2, guard_env, c,
                                               body3))
                                      else
                                        (let body3 =
                                           FStar_Syntax_Util.abs more_bs
                                             body2
                                             FStar_Pervasives_Native.None
                                            in
                                         (env_bs, bs2, guard_env, c, body3)))
                              in
                           let uu____13253 =
                             tc_abs_check_binders env1 bs1 bs_expected2  in
                           handle_more uu____13253 c_expected1 body1  in
                         let mk_letrec_env envbody bs1 c =
                           let letrecs = guard_letrecs envbody bs1 c  in
                           let envbody1 =
                             let uu___1821_13318 = envbody  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1821_13318.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1821_13318.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1821_13318.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1821_13318.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1821_13318.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1821_13318.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1821_13318.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1821_13318.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1821_13318.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1821_13318.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1821_13318.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1821_13318.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1821_13318.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs = [];
                               FStar_TypeChecker_Env.top_level =
                                 (uu___1821_13318.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1821_13318.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___1821_13318.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (uu___1821_13318.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1821_13318.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1821_13318.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1821_13318.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1821_13318.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1821_13318.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1821_13318.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1821_13318.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1821_13318.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1821_13318.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1821_13318.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1821_13318.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1821_13318.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1821_13318.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1821_13318.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1821_13318.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1821_13318.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1821_13318.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1821_13318.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1821_13318.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1821_13318.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1821_13318.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1821_13318.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1821_13318.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1821_13318.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1821_13318.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1821_13318.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1821_13318.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1821_13318.FStar_TypeChecker_Env.erasable_types_tab)
                             }  in
                           let uu____13325 =
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____13391  ->
                                     fun uu____13392  ->
                                       match (uu____13391, uu____13392) with
                                       | ((env1,letrec_binders,g),(l,t3,u_names))
                                           ->
                                           let uu____13483 =
                                             let uu____13490 =
                                               let uu____13491 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____13491
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____13490 t3  in
                                           (match uu____13483 with
                                            | (t4,uu____13515,g') ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env1 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____13528 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___1839_13531
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___1839_13531.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___1839_13531.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____13528 ::
                                                        letrec_binders
                                                  | uu____13532 ->
                                                      letrec_binders
                                                   in
                                                let uu____13537 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g'
                                                   in
                                                (env2, lb, uu____13537)))
                                  (envbody1, [],
                                    FStar_TypeChecker_Env.trivial_guard))
                              in
                           match uu____13325 with
                           | (envbody2,letrec_binders,g) ->
                               let uu____13557 =
                                 FStar_TypeChecker_Env.close_guard envbody2
                                   bs1 g
                                  in
                               (envbody2, letrec_binders, uu____13557)
                            in
                         let uu____13560 =
                           check_actuals_against_formals env bs bs_expected1
                             body
                            in
                         (match uu____13560 with
                          | (envbody,bs1,g_env,c,body1) ->
                              let uu____13596 = mk_letrec_env envbody bs1 c
                                 in
                              (match uu____13596 with
                               | (envbody1,letrecs,g_annots) ->
                                   let envbody2 =
                                     FStar_TypeChecker_Env.set_expected_typ
                                       envbody1
                                       (FStar_Syntax_Util.comp_result c)
                                      in
                                   let uu____13633 =
                                     FStar_TypeChecker_Env.conj_guard g_env
                                       g_annots
                                      in
                                   ((FStar_Pervasives_Native.Some t2), bs1,
                                     letrecs,
                                     (FStar_Pervasives_Native.Some c),
                                     envbody2, body1, uu____13633))))
                | uu____13640 ->
                    if Prims.op_Negation norm1
                    then
                      let uu____13662 =
                        let uu____13663 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.unfold_whnf env)
                           in
                        FStar_All.pipe_right uu____13663
                          FStar_Syntax_Util.unascribe
                         in
                      as_function_typ true uu____13662
                    else
                      (let uu____13667 =
                         tc_abs_expected_function_typ env bs
                           FStar_Pervasives_Native.None body
                          in
                       match uu____13667 with
                       | (uu____13706,bs1,uu____13708,c_opt,envbody,body1,g_env)
                           ->
                           ((FStar_Pervasives_Native.Some t2), bs1, [],
                             c_opt, envbody, body1, g_env))
                 in
              as_function_typ false t1

and (tc_abs_check_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.binders *
          (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.binders)
          FStar_Util.either FStar_Pervasives_Native.option *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.subst_t))
  =
  fun env  ->
    fun bs  ->
      fun bs_expected  ->
        let rec aux uu____13782 bs1 bs_expected1 =
          match uu____13782 with
          | (env1,subst) ->
              (match (bs1, bs_expected1) with
               | ([],[]) ->
                   (env1, [], FStar_Pervasives_Native.None,
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ((uu____13889,FStar_Pervasives_Native.None )::uu____13890,
                  (hd_e,q)::uu____13893) when
                   FStar_Syntax_Syntax.is_implicit_or_meta q ->
                   let bv =
                     let uu____13945 =
                       let uu____13948 =
                         FStar_Ident.range_of_id
                           hd_e.FStar_Syntax_Syntax.ppname
                          in
                       FStar_Pervasives_Native.Some uu____13948  in
                     let uu____13949 =
                       FStar_Syntax_Subst.subst subst
                         hd_e.FStar_Syntax_Syntax.sort
                        in
                     FStar_Syntax_Syntax.new_bv uu____13945 uu____13949  in
                   aux (env1, subst) ((bv, q) :: bs1) bs_expected1
               | ((hd,imp)::bs2,(hd_expected,imp')::bs_expected2) ->
                   ((let special q1 q2 =
                       match (q1, q2) with
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta
                          uu____14044),FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____14045)) -> true
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Equality )) -> true
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit
                          uu____14060),FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____14061)) -> true
                       | uu____14070 -> false  in
                     let uu____14080 =
                       (Prims.op_Negation (special imp imp')) &&
                         (let uu____14083 =
                            FStar_Syntax_Util.eq_aqual imp imp'  in
                          uu____14083 <> FStar_Syntax_Util.Equal)
                        in
                     if uu____14080
                     then
                       let uu____14085 =
                         let uu____14091 =
                           let uu____14093 =
                             FStar_Syntax_Print.bv_to_string hd  in
                           FStar_Util.format1
                             "Inconsistent implicit argument annotation on argument %s"
                             uu____14093
                            in
                         (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                           uu____14091)
                          in
                       let uu____14097 = FStar_Syntax_Syntax.range_of_bv hd
                          in
                       FStar_Errors.raise_error uu____14085 uu____14097
                     else ());
                    (let expected_t =
                       FStar_Syntax_Subst.subst subst
                         hd_expected.FStar_Syntax_Syntax.sort
                        in
                     let uu____14101 =
                       let uu____14108 =
                         let uu____14109 =
                           FStar_Syntax_Util.unmeta
                             hd.FStar_Syntax_Syntax.sort
                            in
                         uu____14109.FStar_Syntax_Syntax.n  in
                       match uu____14108 with
                       | FStar_Syntax_Syntax.Tm_unknown  ->
                           (expected_t, FStar_TypeChecker_Env.trivial_guard)
                       | uu____14120 ->
                           ((let uu____14122 =
                               FStar_TypeChecker_Env.debug env1
                                 FStar_Options.High
                                in
                             if uu____14122
                             then
                               let uu____14125 =
                                 FStar_Syntax_Print.bv_to_string hd  in
                               FStar_Util.print1 "Checking binder %s\n"
                                 uu____14125
                             else ());
                            (let uu____14130 =
                               tc_tot_or_gtot_term env1
                                 hd.FStar_Syntax_Syntax.sort
                                in
                             match uu____14130 with
                             | (t,uu____14144,g1_env) ->
                                 let g2_env =
                                   let uu____14147 =
                                     FStar_TypeChecker_Rel.teq_nosmt env1 t
                                       expected_t
                                      in
                                   match uu____14147 with
                                   | FStar_Pervasives_Native.Some g ->
                                       FStar_All.pipe_right g
                                         (FStar_TypeChecker_Rel.resolve_implicits
                                            env1)
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____14151 =
                                         FStar_TypeChecker_Rel.get_subtyping_prop
                                           env1 expected_t t
                                          in
                                       (match uu____14151 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____14154 =
                                              FStar_TypeChecker_Err.basic_type_error
                                                env1
                                                FStar_Pervasives_Native.None
                                                expected_t t
                                               in
                                            let uu____14160 =
                                              FStar_TypeChecker_Env.get_range
                                                env1
                                               in
                                            FStar_Errors.raise_error
                                              uu____14154 uu____14160
                                        | FStar_Pervasives_Native.Some g_env
                                            ->
                                            FStar_TypeChecker_Util.label_guard
                                              (hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                              "Type annotation on parameter incompatible with the expected type"
                                              g_env)
                                    in
                                 let uu____14163 =
                                   FStar_TypeChecker_Env.conj_guard g1_env
                                     g2_env
                                    in
                                 (t, uu____14163)))
                        in
                     match uu____14101 with
                     | (t,g_env) ->
                         let hd1 =
                           let uu___1946_14189 = hd  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1946_14189.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1946_14189.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t
                           }  in
                         let b = (hd1, imp)  in
                         let b_expected = (hd_expected, imp')  in
                         let env_b = push_binding env1 b  in
                         let subst1 =
                           let uu____14212 =
                             FStar_Syntax_Syntax.bv_to_name hd1  in
                           maybe_extend_subst subst b_expected uu____14212
                            in
                         let uu____14215 =
                           aux (env_b, subst1) bs2 bs_expected2  in
                         (match uu____14215 with
                          | (env_bs,bs3,rest,g'_env_b,subst2) ->
                              let g'_env =
                                FStar_TypeChecker_Env.close_guard env_bs 
                                  [b] g'_env_b
                                 in
                              let uu____14280 =
                                FStar_TypeChecker_Env.conj_guard g_env g'_env
                                 in
                              (env_bs, (b :: bs3), rest, uu____14280, subst2))))
               | (rest,[]) ->
                   (env1, [],
                     (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ([],rest) ->
                   (env1, [],
                     (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                     FStar_TypeChecker_Env.trivial_guard, subst))
           in
        aux (env, []) bs bs_expected

and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail msg t =
            let uu____14419 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____14419 top.FStar_Syntax_Syntax.pos
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____14427 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____14427 with
          | (env1,topt) ->
              ((let uu____14447 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____14447
                then
                  let uu____14450 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____14450
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____14464 =
                  tc_abs_expected_function_typ env1 bs topt body  in
                match uu____14464 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____14505 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____14505
                      then
                        let uu____14508 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____14513 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____14518 =
                          let uu____14520 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____14520 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____14508 uu____14513 uu____14518
                      else ());
                     (let uu____14530 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____14530
                      then
                        let uu____14535 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____14538 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____14535 uu____14538
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____14544 =
                        let uu____14555 =
                          let uu____14563 =
                            (FStar_All.pipe_right c_opt FStar_Util.is_some)
                              &&
                              (let uu____14573 =
                                 let uu____14574 =
                                   FStar_Syntax_Subst.compress body1  in
                                 uu____14574.FStar_Syntax_Syntax.n  in
                               match uu____14573 with
                               | FStar_Syntax_Syntax.Tm_app (head,args) when
                                   (FStar_List.length args) = Prims.int_one
                                   ->
                                   let uu____14614 =
                                     let uu____14615 =
                                       FStar_Syntax_Subst.compress head  in
                                     uu____14615.FStar_Syntax_Syntax.n  in
                                   (match uu____14614 with
                                    | FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reflect
                                        uu____14619) -> true
                                    | uu____14621 -> false)
                               | uu____14623 -> false)
                             in
                          if uu____14563
                          then
                            let uu____14633 =
                              let uu____14634 =
                                FStar_TypeChecker_Env.clear_expected_typ
                                  envbody1
                                 in
                              FStar_All.pipe_right uu____14634
                                FStar_Pervasives_Native.fst
                               in
                            let uu____14649 =
                              let uu____14650 =
                                let uu____14657 =
                                  let uu____14658 =
                                    let uu____14685 =
                                      let uu____14702 =
                                        let uu____14711 =
                                          FStar_All.pipe_right c_opt
                                            FStar_Util.must
                                           in
                                        FStar_Util.Inr uu____14711  in
                                      (uu____14702,
                                        FStar_Pervasives_Native.None)
                                       in
                                    (body1, uu____14685,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____14658
                                   in
                                FStar_Syntax_Syntax.mk uu____14657  in
                              uu____14650 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            (uu____14633, uu____14649, false)
                          else
                            (let uu____14760 =
                               let uu____14762 =
                                 let uu____14769 =
                                   let uu____14770 =
                                     FStar_Syntax_Subst.compress body1  in
                                   uu____14770.FStar_Syntax_Syntax.n  in
                                 (c_opt, uu____14769)  in
                               match uu____14762 with
                               | (FStar_Pervasives_Native.None
                                  ,FStar_Syntax_Syntax.Tm_ascribed
                                  (uu____14776,(FStar_Util.Inr
                                                expected_c,uu____14778),uu____14779))
                                   -> false
                               | uu____14829 -> true  in
                             (envbody1, body1, uu____14760))
                           in
                        match uu____14555 with
                        | (envbody2,body2,should_check_expected_effect) ->
                            let uu____14853 =
                              tc_term
                                (let uu___2031_14862 = envbody2  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2031_14862.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2031_14862.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2031_14862.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2031_14862.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2031_14862.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2031_14862.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2031_14862.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2031_14862.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2031_14862.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2031_14862.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2031_14862.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2031_14862.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2031_14862.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2031_14862.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level = false;
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2031_14862.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___2031_14862.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2031_14862.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2031_14862.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___2031_14862.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2031_14862.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2031_14862.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2031_14862.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2031_14862.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2031_14862.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2031_14862.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2031_14862.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2031_14862.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2031_14862.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2031_14862.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2031_14862.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2031_14862.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2031_14862.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2031_14862.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2031_14862.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___2031_14862.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2031_14862.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___2031_14862.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2031_14862.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2031_14862.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2031_14862.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2031_14862.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2031_14862.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___2031_14862.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___2031_14862.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) body2
                               in
                            (match uu____14853 with
                             | (body3,cbody,guard_body) ->
                                 let guard_body1 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     envbody2 guard_body
                                    in
                                 if should_check_expected_effect
                                 then
                                   let uu____14889 =
                                     FStar_TypeChecker_Common.lcomp_comp
                                       cbody
                                      in
                                   (match uu____14889 with
                                    | (cbody1,g_lc) ->
                                        let uu____14906 =
                                          check_expected_effect
                                            (let uu___2042_14915 = envbody2
                                                in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 use_eq;
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.lax);
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.phase1);
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___2042_14915.FStar_TypeChecker_Env.erasable_types_tab)
                                             }) c_opt (body3, cbody1)
                                           in
                                        (match uu____14906 with
                                         | (body4,cbody2,guard) ->
                                             let uu____14929 =
                                               let uu____14930 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_lc guard
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 guard_body1 uu____14930
                                                in
                                             (body4, cbody2, uu____14929)))
                                 else
                                   (let uu____14937 =
                                      FStar_TypeChecker_Common.lcomp_comp
                                        cbody
                                       in
                                    match uu____14937 with
                                    | (cbody1,g_lc) ->
                                        let uu____14954 =
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 g_lc
                                           in
                                        (body3, cbody1, uu____14954)))
                         in
                      match uu____14544 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____14977 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14980 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____14980)
                               in
                            if uu____14977
                            then
                              let uu____14983 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____14984 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____14983
                                uu____14984
                            else
                              (let guard =
                                 let uu____14988 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14988
                                  in
                               guard)
                             in
                          let guard1 =
                            FStar_TypeChecker_Util.close_guard_implicits env1
                              false bs1 guard
                             in
                          let tfun_computed =
                            FStar_Syntax_Util.arrow bs1 cbody  in
                          let e =
                            FStar_Syntax_Util.abs bs1 body2
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_comp_of_comp
                                    (FStar_Util.dflt cbody c_opt)))
                             in
                          let uu____15003 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                let t_annot =
                                  match topt with
                                  | FStar_Pervasives_Native.Some t2 -> t2
                                  | FStar_Pervasives_Native.None  ->
                                      failwith
                                        "Impossible! tc_abs: if tfun_computed is Some, expected topt to also be Some"
                                   in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____15027
                                     -> (e, t_annot, guard1)
                                 | uu____15042 ->
                                     let lc =
                                       let uu____15044 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed
                                          in
                                       FStar_All.pipe_right uu____15044
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let uu____15045 =
                                       FStar_TypeChecker_Util.check_has_type
                                         env1 e lc t1
                                        in
                                     (match uu____15045 with
                                      | (e1,uu____15059,guard') ->
                                          let uu____15061 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t_annot, uu____15061)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____15003 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____15072 =
                                 let uu____15077 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____15077 guard2
                                  in
                               (match uu____15072 with
                                | (c1,g) -> (e1, c1, g)))))))

and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
                FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun head  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = FStar_Syntax_Util.comp_result chead  in
              (let uu____15128 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____15128
               then
                 let uu____15131 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos
                    in
                 let uu____15133 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____15131
                   uu____15133
               else ());
              (let monadic_application uu____15215 subst arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____15215 with
                 | (head1,chead1,ghead1,cres) ->
                     let uu____15284 =
                       check_no_escape (FStar_Pervasives_Native.Some head1)
                         env fvs (FStar_Syntax_Util.comp_result cres)
                        in
                     (match uu____15284 with
                      | (rt,g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt  in
                          let uu____15298 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____15314 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____15314
                                   in
                                (cres1, g)
                            | uu____15315 ->
                                let g =
                                  let uu____15325 =
                                    let uu____15326 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____15326
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____15325
                                   in
                                let uu____15327 =
                                  let uu____15328 =
                                    FStar_Syntax_Util.arrow bs cres1  in
                                  FStar_Syntax_Syntax.mk_Total uu____15328
                                   in
                                (uu____15327, g)
                             in
                          (match uu____15298 with
                           | (cres2,guard1) ->
                               ((let uu____15338 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium
                                    in
                                 if uu____15338
                                 then
                                   let uu____15341 =
                                     FStar_Syntax_Print.comp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____15341
                                 else ());
                                (let uu____15346 =
                                   let uu____15351 =
                                     let uu____15352 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         chead1
                                        in
                                     FStar_All.pipe_right uu____15352
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   let uu____15353 =
                                     let uu____15354 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         cres2
                                        in
                                     FStar_All.pipe_right uu____15354
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   (uu____15351, uu____15353)  in
                                 match uu____15346 with
                                 | (chead2,cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____15378  ->
                                                 match uu____15378 with
                                                 | (uu____15388,uu____15389,lc)
                                                     ->
                                                     (let uu____15397 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc
                                                         in
                                                      Prims.op_Negation
                                                        uu____15397)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev)
                                          in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head1
                                           (FStar_List.rev arg_rets_rev)
                                           FStar_Pervasives_Native.None
                                           head1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____15410 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful
                                          in
                                       if uu____15410
                                       then
                                         ((let uu____15414 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15414
                                           then
                                             let uu____15417 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____15417
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____15425 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15425
                                           then
                                             let uu____15428 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____15428
                                           else ());
                                          cres3)
                                        in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c  ->
                                            fun uu____15459  ->
                                              match uu____15459 with
                                              | ((e,q),x,c) ->
                                                  ((let uu____15501 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15501
                                                    then
                                                      let uu____15504 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                             -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1
                                                         in
                                                      let uu____15509 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15511 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____15504
                                                        uu____15509
                                                        uu____15511
                                                    else ());
                                                   (let uu____15516 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15516
                                                    then
                                                      FStar_TypeChecker_Util.bind
                                                        e.FStar_Syntax_Syntax.pos
                                                        env
                                                        (FStar_Pervasives_Native.Some
                                                           e) c (x, out_c)
                                                    else
                                                      FStar_TypeChecker_Util.bind
                                                        e.FStar_Syntax_Syntax.pos
                                                        env
                                                        FStar_Pervasives_Native.None
                                                        c (x, out_c)))) cres4
                                         arg_comps_rev
                                        in
                                     let comp1 =
                                       (let uu____15527 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____15527
                                        then
                                          let uu____15530 =
                                            FStar_Syntax_Print.term_to_string
                                              head1
                                             in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____15530
                                        else ());
                                       (let uu____15535 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2
                                           in
                                        if uu____15535
                                        then
                                          FStar_TypeChecker_Util.bind
                                            head1.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some
                                               head1) chead2
                                            (FStar_Pervasives_Native.None,
                                              comp)
                                        else
                                          FStar_TypeChecker_Util.bind
                                            head1.FStar_Syntax_Syntax.pos env
                                            FStar_Pervasives_Native.None
                                            chead2
                                            (FStar_Pervasives_Native.None,
                                              comp))
                                        in
                                     let shortcuts_evaluation_order =
                                       let uu____15546 =
                                         let uu____15547 =
                                           FStar_Syntax_Subst.compress head1
                                            in
                                         uu____15547.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15546 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____15552 -> false  in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1  ->
                                                fun uu____15575  ->
                                                  match uu____15575 with
                                                  | (arg,uu____15589,uu____15590)
                                                      -> arg :: args1) []
                                             arg_comps_rev
                                            in
                                         let app =
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             head1 args1
                                             FStar_Pervasives_Native.None r
                                            in
                                         let app1 =
                                           FStar_TypeChecker_Util.maybe_lift
                                             env app
                                             cres4.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.res_typ
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env app1
                                           comp1.FStar_TypeChecker_Common.eff_name
                                           comp1.FStar_TypeChecker_Common.res_typ
                                       else
                                         (let uu____15601 =
                                            let map_fun uu____15667 =
                                              match uu____15667 with
                                              | ((e,q),uu____15708,c) ->
                                                  ((let uu____15731 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15731
                                                    then
                                                      let uu____15734 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15736 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____15734
                                                        uu____15736
                                                    else ());
                                                   (let uu____15741 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15741
                                                    then
                                                      ((let uu____15767 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15767
                                                        then
                                                          FStar_Util.print_string
                                                            "... not lifting\n"
                                                        else ());
                                                       (FStar_Pervasives_Native.None,
                                                         (e, q)))
                                                    else
                                                      (let warn_effectful_args
                                                         =
                                                         (FStar_TypeChecker_Util.must_erase_for_extraction
                                                            env
                                                            chead2.FStar_TypeChecker_Common.res_typ)
                                                           &&
                                                           (let uu____15808 =
                                                              let uu____15810
                                                                =
                                                                let uu____15811
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head1
                                                                   in
                                                                uu____15811.FStar_Syntax_Syntax.n
                                                                 in
                                                              match uu____15810
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____15816
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore"
                                                                     in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____15816
                                                              | uu____15818
                                                                  -> true
                                                               in
                                                            Prims.op_Negation
                                                              uu____15808)
                                                          in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____15822 =
                                                            let uu____15828 =
                                                              let uu____15830
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e
                                                                 in
                                                              let uu____15832
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  c.FStar_TypeChecker_Common.eff_name
                                                                 in
                                                              let uu____15834
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____15830
                                                                uu____15832
                                                                uu____15834
                                                               in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____15828)
                                                             in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____15822)
                                                       else ();
                                                       (let uu____15841 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15841
                                                        then
                                                          FStar_Util.print_string
                                                            "... lifting!\n"
                                                        else ());
                                                       (let x =
                                                          FStar_Syntax_Syntax.new_bv
                                                            FStar_Pervasives_Native.None
                                                            c.FStar_TypeChecker_Common.res_typ
                                                           in
                                                        let e1 =
                                                          FStar_TypeChecker_Util.maybe_lift
                                                            env e
                                                            c.FStar_TypeChecker_Common.eff_name
                                                            comp1.FStar_TypeChecker_Common.eff_name
                                                            c.FStar_TypeChecker_Common.res_typ
                                                           in
                                                        let uu____15849 =
                                                          let uu____15858 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          (uu____15858, q)
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____15849)))))
                                               in
                                            let uu____15887 =
                                              let uu____15918 =
                                                let uu____15947 =
                                                  let uu____15958 =
                                                    let uu____15967 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head1
                                                       in
                                                    (uu____15967,
                                                      FStar_Pervasives_Native.None,
                                                      chead2)
                                                     in
                                                  uu____15958 ::
                                                    arg_comps_rev
                                                   in
                                                FStar_List.map map_fun
                                                  uu____15947
                                                 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____15918
                                               in
                                            match uu____15887 with
                                            | (lifted_args,reverse_args) ->
                                                let uu____16168 =
                                                  let uu____16169 =
                                                    FStar_List.hd
                                                      reverse_args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____16169
                                                   in
                                                let uu____16190 =
                                                  let uu____16191 =
                                                    FStar_List.tl
                                                      reverse_args
                                                     in
                                                  FStar_List.rev uu____16191
                                                   in
                                                (lifted_args, uu____16168,
                                                  uu____16190)
                                             in
                                          match uu____15601 with
                                          | (lifted_args,head2,args1) ->
                                              let app =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  head2 args1
                                                  FStar_Pervasives_Native.None
                                                  r
                                                 in
                                              let app1 =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env app
                                                  cres4.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ
                                                 in
                                              let app2 =
                                                FStar_TypeChecker_Util.maybe_monadic
                                                  env app1
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ
                                                 in
                                              let bind_lifted_args e
                                                uu___6_16302 =
                                                match uu___6_16302 with
                                                | FStar_Pervasives_Native.None
                                                     -> e
                                                | FStar_Pervasives_Native.Some
                                                    (x,m,t,e1) ->
                                                    let lb =
                                                      FStar_Syntax_Util.mk_letbinding
                                                        (FStar_Util.Inl x) []
                                                        t m e1 []
                                                        e1.FStar_Syntax_Syntax.pos
                                                       in
                                                    let letbinding =
                                                      let uu____16363 =
                                                        let uu____16370 =
                                                          let uu____16371 =
                                                            let uu____16385 =
                                                              let uu____16388
                                                                =
                                                                let uu____16389
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x
                                                                   in
                                                                [uu____16389]
                                                                 in
                                                              FStar_Syntax_Subst.close
                                                                uu____16388 e
                                                               in
                                                            ((false, [lb]),
                                                              uu____16385)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_let
                                                            uu____16371
                                                           in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____16370
                                                         in
                                                      uu____16363
                                                        FStar_Pervasives_Native.None
                                                        e.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (letbinding,
                                                           (FStar_Syntax_Syntax.Meta_monadic
                                                              (m,
                                                                (comp1.FStar_TypeChecker_Common.res_typ)))))
                                                      FStar_Pervasives_Native.None
                                                      e.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_List.fold_left
                                                bind_lifted_args app2
                                                lifted_args)
                                        in
                                     let uu____16441 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1
                                        in
                                     (match uu____16441 with
                                      | (comp2,g) ->
                                          ((let uu____16459 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme
                                               in
                                            if uu____16459
                                            then
                                              let uu____16462 =
                                                FStar_Syntax_Print.term_to_string
                                                  app
                                                 in
                                              let uu____16464 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2
                                                 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____16462 uu____16464
                                            else ());
                                           (app, comp2, g)))))))
                  in
               let rec tc_args head_info uu____16553 bs args1 =
                 match uu____16553 with
                 | (subst,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____16716))::rest,
                         (uu____16718,FStar_Pervasives_Native.None )::uu____16719)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____16780 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head) env fvs t
                             in
                          (match uu____16780 with
                           | (t1,g_ex) ->
                               let r1 =
                                 match outargs with
                                 | [] -> head.FStar_Syntax_Syntax.pos
                                 | ((t2,uu____16811),uu____16812,uu____16813)::uu____16814
                                     ->
                                     let uu____16869 =
                                       FStar_Range.def_range
                                         head.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____16870 =
                                       let uu____16871 =
                                         FStar_Range.use_range
                                           head.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____16872 =
                                         FStar_Range.use_range
                                           t2.FStar_Syntax_Syntax.pos
                                          in
                                       FStar_Range.union_rng uu____16871
                                         uu____16872
                                        in
                                     FStar_Range.range_of_rng uu____16869
                                       uu____16870
                                  in
                               let uu____16873 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   r1 env t1
                                  in
                               (match uu____16873 with
                                | (varg,uu____16894,implicits) ->
                                    let subst1 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst  in
                                    let arg =
                                      let uu____16922 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____16922)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____16931 =
                                      let uu____16974 =
                                        let uu____16993 =
                                          let uu____17010 =
                                            let uu____17011 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____17011
                                              FStar_TypeChecker_Common.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____17010)
                                           in
                                        uu____16993 :: outargs  in
                                      (subst1, uu____16974, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____16931 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____17081,FStar_Pervasives_Native.None
                                                                 )::uu____17082)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst tau  in
                          let uu____17144 =
                            tc_tactic FStar_Syntax_Syntax.t_unit
                              FStar_Syntax_Syntax.t_unit env tau1
                             in
                          (match uu____17144 with
                           | (tau2,uu____17158,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____17161 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head) env
                                   fvs t
                                  in
                               (match uu____17161 with
                                | (t1,g_ex) ->
                                    let r1 =
                                      match outargs with
                                      | [] -> head.FStar_Syntax_Syntax.pos
                                      | ((t2,uu____17192),uu____17193,uu____17194)::uu____17195
                                          ->
                                          let uu____17250 =
                                            FStar_Range.def_range
                                              head.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____17251 =
                                            let uu____17252 =
                                              FStar_Range.use_range
                                                head.FStar_Syntax_Syntax.pos
                                               in
                                            let uu____17253 =
                                              FStar_Range.use_range
                                                t2.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Range.union_rng uu____17252
                                              uu____17253
                                             in
                                          FStar_Range.range_of_rng
                                            uu____17250 uu____17251
                                       in
                                    let uu____17254 =
                                      let uu____17267 =
                                        let uu____17274 =
                                          let uu____17279 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____17279, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____17274
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        r1 env t1 FStar_Syntax_Syntax.Strict
                                        uu____17267
                                       in
                                    (match uu____17254 with
                                     | (varg,uu____17292,implicits) ->
                                         let subst1 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst  in
                                         let arg =
                                           let uu____17320 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____17320)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____17329 =
                                           let uu____17372 =
                                             let uu____17391 =
                                               let uu____17408 =
                                                 let uu____17409 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____17409
                                                   FStar_TypeChecker_Common.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____17408)
                                                in
                                             uu____17391 :: outargs  in
                                           (subst1, uu____17372, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____17329 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____17549,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____17550)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____17561),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____17562)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____17570),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____17571)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____17586 ->
                                let uu____17595 =
                                  let uu____17601 =
                                    let uu____17603 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____17605 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____17607 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____17609 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____17603 uu____17605 uu____17607
                                      uu____17609
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____17601)
                                   in
                                FStar_Errors.raise_error uu____17595
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst aqual  in
                            let x1 =
                              let uu___2341_17616 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2341_17616.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2341_17616.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____17618 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____17618
                             then
                               let uu____17621 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____17623 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____17625 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17627 =
                                 FStar_Syntax_Print.subst_to_string subst  in
                               let uu____17629 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____17621 uu____17623 uu____17625
                                 uu____17627 uu____17629
                             else ());
                            (let uu____17634 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head) env fvs
                                 targ
                                in
                             match uu____17634 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2350_17649 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2350_17649.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2350_17649.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2350_17649.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2350_17649.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2350_17649.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2350_17649.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2350_17649.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2350_17649.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2350_17649.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2350_17649.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2350_17649.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2350_17649.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2350_17649.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2350_17649.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2350_17649.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2350_17649.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___2350_17649.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2350_17649.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2350_17649.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2350_17649.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2350_17649.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2350_17649.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2350_17649.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2350_17649.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2350_17649.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2350_17649.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2350_17649.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2350_17649.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2350_17649.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2350_17649.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2350_17649.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2350_17649.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2350_17649.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2350_17649.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2350_17649.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2350_17649.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2350_17649.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2350_17649.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2350_17649.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2350_17649.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2350_17649.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2350_17649.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2350_17649.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2350_17649.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2350_17649.FStar_TypeChecker_Env.erasable_types_tab)
                                   }  in
                                 ((let uu____17651 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____17651
                                   then
                                     let uu____17654 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____17656 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____17658 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     let uu____17660 =
                                       FStar_Util.string_of_bool
                                         env2.FStar_TypeChecker_Env.use_eq
                                        in
                                     FStar_Util.print4
                                       "Checking arg (%s) %s at type %s with use_eq:%s\n"
                                       uu____17654 uu____17656 uu____17658
                                       uu____17660
                                   else ());
                                  (let uu____17665 = tc_term env2 e  in
                                   match uu____17665 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____17682 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____17682
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____17705 =
                                           let uu____17708 =
                                             let uu____17717 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____17717
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____17708
                                            in
                                         (uu____17705, aq)  in
                                       let uu____17726 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name)
                                          in
                                       if uu____17726
                                       then
                                         let subst1 =
                                           let uu____17736 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst
                                             uu____17736 e1
                                            in
                                         tc_args head_info
                                           (subst1,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, fvs)
                                           rest rest'
                                       else
                                         tc_args head_info
                                           (subst,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, (x1 ::
                                             fvs)) rest rest')))))
                      | (uu____17883,[]) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____17919) ->
                          let uu____17970 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs []
                             in
                          (match uu____17970 with
                           | (head1,chead1,ghead1) ->
                               let uu____17992 =
                                 let uu____17997 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1
                                    in
                                 FStar_All.pipe_right uu____17997
                                   (fun uu____18014  ->
                                      match uu____18014 with
                                      | (c,g1) ->
                                          let uu____18025 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1
                                             in
                                          (c, uu____18025))
                                  in
                               (match uu____17992 with
                                | (chead2,ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____18068 =
                                          FStar_Syntax_Subst.compress tres
                                           in
                                        FStar_All.pipe_right uu____18068
                                          FStar_Syntax_Util.unrefine
                                         in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1,cres') ->
                                          let uu____18099 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres'
                                             in
                                          (match uu____18099 with
                                           | (bs2,cres'1) ->
                                               let head_info1 =
                                                 (head1, chead2, ghead3,
                                                   cres'1)
                                                  in
                                               ((let uu____18122 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low
                                                    in
                                                 if uu____18122
                                                 then
                                                   FStar_Errors.log_issue
                                                     tres1.FStar_Syntax_Syntax.pos
                                                     (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                       "Potentially redundant explicit currying of a function type")
                                                 else ());
                                                tc_args head_info1
                                                  ([], [], [],
                                                    FStar_TypeChecker_Env.trivial_guard,
                                                    []) bs2 args1))
                                      | uu____18185 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____18193 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env)
                                                 in
                                              FStar_All.pipe_right
                                                uu____18193
                                                FStar_Syntax_Util.unascribe
                                               in
                                            let uu____18194 =
                                              let uu____18195 =
                                                FStar_Syntax_Subst.compress
                                                  tres3
                                                 in
                                              uu____18195.FStar_Syntax_Syntax.n
                                               in
                                            match uu____18194 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____18198;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____18199;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},uu____18201)
                                                -> norm_tres tres4
                                            | uu____18209 -> tres3  in
                                          let uu____18210 = norm_tres tres1
                                             in
                                          aux true solve ghead3 uu____18210
                                      | uu____18212 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3
                                             in
                                          aux norm1 true ghead4 tres1
                                      | uu____18215 ->
                                          let uu____18216 =
                                            let uu____18222 =
                                              let uu____18224 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead
                                                 in
                                              let uu____18226 =
                                                FStar_Util.string_of_int
                                                  n_args
                                                 in
                                              let uu____18228 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1
                                                 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____18224 uu____18226
                                                uu____18228
                                               in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____18222)
                                             in
                                          let uu____18232 =
                                            FStar_Syntax_Syntax.argpos arg
                                             in
                                          FStar_Errors.raise_error
                                            uu____18216 uu____18232
                                       in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2))))
                  in
               let rec check_function_app tf guard =
                 let uu____18262 =
                   let uu____18263 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____18263.FStar_Syntax_Syntax.n  in
                 match uu____18262 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____18272 ->
                     let uu____18285 =
                       FStar_List.fold_right
                         (fun uu____18316  ->
                            fun uu____18317  ->
                              match uu____18317 with
                              | (bs,guard1) ->
                                  let uu____18344 =
                                    let uu____18357 =
                                      let uu____18358 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____18358
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____18357
                                     in
                                  (match uu____18344 with
                                   | (t,uu____18375,g) ->
                                       let uu____18389 =
                                         let uu____18392 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____18392 :: bs  in
                                       let uu____18393 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____18389, uu____18393))) args
                         ([], guard)
                        in
                     (match uu____18285 with
                      | (bs,guard1) ->
                          let uu____18410 =
                            let uu____18417 =
                              let uu____18430 =
                                let uu____18431 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____18431
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____18430
                               in
                            match uu____18417 with
                            | (t,uu____18448,g) ->
                                let uu____18462 = FStar_Options.ml_ish ()  in
                                if uu____18462
                                then
                                  let uu____18471 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____18474 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____18471, uu____18474)
                                else
                                  (let uu____18479 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____18482 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____18479, uu____18482))
                             in
                          (match uu____18410 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____18501 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____18501
                                 then
                                   let uu____18505 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let uu____18507 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____18509 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____18505 uu____18507 uu____18509
                                 else ());
                                (let g =
                                   let uu____18515 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____18515
                                    in
                                 let uu____18516 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____18516))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____18517;
                        FStar_Syntax_Syntax.pos = uu____18518;
                        FStar_Syntax_Syntax.vars = uu____18519;_},uu____18520)
                     ->
                     let uu____18557 =
                       FStar_List.fold_right
                         (fun uu____18588  ->
                            fun uu____18589  ->
                              match uu____18589 with
                              | (bs,guard1) ->
                                  let uu____18616 =
                                    let uu____18629 =
                                      let uu____18630 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____18630
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____18629
                                     in
                                  (match uu____18616 with
                                   | (t,uu____18647,g) ->
                                       let uu____18661 =
                                         let uu____18664 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____18664 :: bs  in
                                       let uu____18665 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____18661, uu____18665))) args
                         ([], guard)
                        in
                     (match uu____18557 with
                      | (bs,guard1) ->
                          let uu____18682 =
                            let uu____18689 =
                              let uu____18702 =
                                let uu____18703 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____18703
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____18702
                               in
                            match uu____18689 with
                            | (t,uu____18720,g) ->
                                let uu____18734 = FStar_Options.ml_ish ()  in
                                if uu____18734
                                then
                                  let uu____18743 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____18746 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____18743, uu____18746)
                                else
                                  (let uu____18751 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____18754 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____18751, uu____18754))
                             in
                          (match uu____18682 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____18773 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____18773
                                 then
                                   let uu____18777 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let uu____18779 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____18781 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____18777 uu____18779 uu____18781
                                 else ());
                                (let g =
                                   let uu____18787 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____18787
                                    in
                                 let uu____18788 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____18788))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____18811 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____18811 with
                      | (bs1,c1) ->
                          let head_info = (head, chead, ghead, c1)  in
                          ((let uu____18834 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____18834
                            then
                              let uu____18837 =
                                FStar_Syntax_Print.term_to_string head  in
                              let uu____18839 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____18841 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____18844 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____18837 uu____18839 uu____18841
                                uu____18844
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____18906) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____18912,uu____18913) ->
                     check_function_app t guard
                 | uu____18954 ->
                     let uu____18955 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____18955
                       head.FStar_Syntax_Syntax.pos
                  in
               check_function_app thead FStar_TypeChecker_Env.trivial_guard)

and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
                FStar_TypeChecker_Common.guard_t))
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
                  (FStar_Syntax_Util.comp_result chead)
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c  in
                  let uu____19038 =
                    FStar_List.fold_left2
                      (fun uu____19107  ->
                         fun uu____19108  ->
                           fun uu____19109  ->
                             match (uu____19107, uu____19108, uu____19109)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____19262 =
                                     let uu____19264 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____19264 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____19262
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____19270 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                       "arguments to short circuiting operators must be pure or ghost"
                                      in
                                   match uu____19270 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen
                                          in
                                       let g1 =
                                         let uu____19300 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____19300 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____19305 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____19305)
                                              &&
                                              (let uu____19308 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name
                                                  in
                                               Prims.op_Negation uu____19308))
                                          in
                                       let uu____19310 =
                                         let uu____19321 =
                                           let uu____19332 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____19332]  in
                                         FStar_List.append seen uu____19321
                                          in
                                       let uu____19365 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____19310, uu____19365, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____19038 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____19433 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____19433
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c  in
                       let uu____19436 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____19436 with | (c2,g) -> (e, c2, g)))
              | uu____19453 ->
                  check_application_args env head chead g_head args
                    expected_topt

and (tc_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list *
          FStar_Syntax_Syntax.term Prims.list * FStar_TypeChecker_Env.env *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Common.guard_t * Prims.bool))
  =
  fun env  ->
    fun pat_t  ->
      fun p0  ->
        let fail msg =
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MismatchedPatternType, msg)
            p0.FStar_Syntax_Syntax.p
           in
        let expected_pat_typ env1 pos scrutinee_t =
          let rec aux norm1 t =
            let t1 = FStar_Syntax_Util.unrefine t  in
            let uu____19551 = FStar_Syntax_Util.head_and_args t1  in
            match uu____19551 with
            | (head,args) ->
                let uu____19594 =
                  let uu____19595 = FStar_Syntax_Subst.compress head  in
                  uu____19595.FStar_Syntax_Syntax.n  in
                (match uu____19594 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____19599;
                        FStar_Syntax_Syntax.vars = uu____19600;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____19607 ->
                     if norm1
                     then t1
                     else
                       (let uu____19611 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____19611))
          
          and unfold_once t f us args =
            let uu____19629 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____19629
            then t
            else
              (let uu____19634 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____19634 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____19654 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____19654 with
                    | (uu____19659,head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            FStar_Pervasives_Native.None
                            t.FStar_Syntax_Syntax.pos
                           in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t'
                           in
                        aux false t'1))
           in
          let uu____19666 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____19666  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____19685 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19685
           then
             let uu____19690 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____19692 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____19690 uu____19692
           else ());
          (let fail1 msg =
             let msg1 =
               let uu____19712 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____19714 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____19712 uu____19714 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____19718 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____19718 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____19762 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____19762 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____19763;
                    FStar_Syntax_Syntax.pos = uu____19764;
                    FStar_Syntax_Syntax.vars = uu____19765;_} ->
                    let uu____19768 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____19768 with
                     | (head_p,args_p) ->
                         let uu____19811 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____19811
                         then
                           let uu____19814 =
                             let uu____19815 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____19815.FStar_Syntax_Syntax.n  in
                           (match uu____19814 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____19820 =
                                    let uu____19822 =
                                      let uu____19824 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____19824
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____19822
                                     in
                                  if uu____19820
                                  then
                                    fail1
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail1 ""
                                 else ();
                                 (let uu____19852 =
                                    let uu____19877 =
                                      let uu____19881 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____19881
                                       in
                                    match uu____19877 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n ->
                                        let uu____19930 =
                                          FStar_Util.first_N n args_p  in
                                        (match uu____19930 with
                                         | (params_p,uu____19988) ->
                                             let uu____20029 =
                                               FStar_Util.first_N n args_s
                                                in
                                             (match uu____20029 with
                                              | (params_s,uu____20087) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____19852 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____20216  ->
                                             fun uu____20217  ->
                                               match (uu____20216,
                                                       uu____20217)
                                               with
                                               | ((p,uu____20251),(s,uu____20253))
                                                   ->
                                                   let uu____20286 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____20286 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____20289 =
                                                          let uu____20291 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____20293 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____20291
                                                            uu____20293
                                                           in
                                                        fail1 uu____20289
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g
                                                           in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____20298 ->
                                fail1 "Pattern matching a non-inductive type")
                         else
                           (let uu____20302 =
                              let uu____20304 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____20306 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____20304 uu____20306
                               in
                            fail1 uu____20302))
                | uu____20309 ->
                    let uu____20310 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____20310 with
                     | FStar_Pervasives_Native.None  -> fail1 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____20353 = FStar_Syntax_Util.head_and_args e  in
          match uu____20353 with
          | (head,args) ->
              (match head.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____20423 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____20423 with
                    | (us,t_f) ->
                        let uu____20443 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____20443 with
                         | (formals,t) ->
                             let erasable =
                               FStar_TypeChecker_Env.non_informative env1 t
                                in
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____20556 formals1 args1 =
                                 match uu____20556 with
                                 | (subst,args_out,bvs,guard) ->
                                     (match (formals1, args1) with
                                      | ([],[]) ->
                                          let head1 =
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              head us
                                             in
                                          let pat_e =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head1 args_out
                                              FStar_Pervasives_Native.None
                                              e.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____20707 =
                                            FStar_Syntax_Subst.subst subst t
                                             in
                                          (pat_e, uu____20707, bvs, guard,
                                            erasable)
                                      | ((f1,uu____20714)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____20772 =
                                            let uu____20793 =
                                              let uu____20794 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____20794.FStar_Syntax_Syntax.n
                                               in
                                            match uu____20793 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2657_20819 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2657_20819.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2657_20819.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      = t_f1
                                                  }  in
                                                let a1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x1
                                                   in
                                                let subst1 =
                                                  (FStar_Syntax_Syntax.NT
                                                     (f1, a1))
                                                  :: subst  in
                                                ((a1, imp_a), subst1,
                                                  (FStar_List.append bvs [x1]),
                                                  FStar_TypeChecker_Env.trivial_guard)
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____20842 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____20856 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____20856 with
                                                 | (a1,uu____20884,g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g
                                                        in
                                                     let subst1 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst  in
                                                     ((a1, imp_a), subst1,
                                                       bvs, g1))
                                            | uu____20908 ->
                                                fail "Not a simple pattern"
                                             in
                                          (match uu____20772 with
                                           | (a1,subst1,bvs1,g) ->
                                               let uu____20973 =
                                                 let uu____20996 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst1,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____20996)
                                                  in
                                               aux uu____20973 formals2 args2)
                                      | uu____21035 ->
                                          fail "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____21094 -> fail "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____21160 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____21160
           then
             let uu____21165 = FStar_Syntax_Print.pat_to_string p  in
             let uu____21167 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____21165
               uu____21167
           else ());
          (let id =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None
              in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____21192 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t
                  in
               FStar_All.pipe_right uu____21192 FStar_Syntax_Syntax.mk_binder
                in
             let tm =
               let uu____21203 =
                 let uu____21208 =
                   let uu____21209 =
                     let uu____21218 =
                       let uu____21219 =
                         FStar_All.pipe_right x_b FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____21219
                         FStar_Syntax_Syntax.bv_to_name
                        in
                     FStar_All.pipe_right uu____21218
                       FStar_Syntax_Syntax.as_arg
                      in
                   [uu____21209]  in
                 FStar_Syntax_Syntax.mk_Tm_app disc uu____21208  in
               uu____21203 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             let tm1 =
               let uu____21255 =
                 let uu____21260 =
                   let uu____21261 =
                     FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg  in
                   [uu____21261]  in
                 FStar_Syntax_Syntax.mk_Tm_app inner_t uu____21260  in
               uu____21255 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None  in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____21323 ->
               let uu____21330 =
                 let uu____21332 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____21332
                  in
               failwith uu____21330
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2696_21354 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2696_21354.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2696_21354.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____21355 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id], uu____21355,
                 (let uu___2699_21362 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2699_21362.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2703_21366 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2703_21366.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2703_21366.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____21367 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id], uu____21367,
                 (let uu___2706_21374 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2706_21374.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant uu____21376 ->
               let uu____21377 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____21377 with
                | (uu____21406,e_c,uu____21408,uu____21409) ->
                    let uu____21414 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____21414 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____21444 =
                              let uu____21446 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t
                                 in
                              Prims.op_Negation uu____21446  in
                            if uu____21444
                            then
                              let uu____21449 =
                                let uu____21451 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ
                                   in
                                let uu____21453 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____21451 uu____21453
                                 in
                              fail uu____21449
                            else ());
                           ([], [], e_c1, p,
                             FStar_TypeChecker_Env.trivial_guard, false)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____21515  ->
                        match uu____21515 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____21545
                                 -> (p1, b)
                             | uu____21555 ->
                                 let uu____21556 =
                                   let uu____21559 =
                                     let uu____21560 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____21560
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____21559
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____21556, b))) sub_pats
                    in
                 let uu___2734_21564 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2734_21564.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____21609  ->
                         match uu____21609 with
                         | (x,uu____21619) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____21627
                                  -> false
                              | uu____21635 -> true)))
                  in
               let uu____21637 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____21637 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____21681 =
                          let uu____21683 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____21685 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____21687 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____21694 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____21683 uu____21685 uu____21687 uu____21694
                           in
                        failwith uu____21681)
                     else ();
                     (let uu____21699 =
                        let uu____21711 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____21711 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard,erasable)
                            ->
                            let g' =
                              let uu____21748 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____21748  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____21751 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____21751
                              then
                                let uu____21756 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____21758 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____21760 =
                                  let uu____21762 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____21770 =
                                           let uu____21772 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____21774 =
                                             let uu____21776 =
                                               let uu____21778 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____21778 ")"
                                                in
                                             Prims.op_Hat " : " uu____21776
                                              in
                                           Prims.op_Hat uu____21772
                                             uu____21774
                                            in
                                         Prims.op_Hat "(" uu____21770)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____21762
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____21756 uu____21758 uu____21760
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable))
                         in
                      match uu____21699 with
                      | (simple_pat_e1,simple_bvs1,g1,erasable) ->
                          let uu____21821 =
                            let uu____21853 =
                              let uu____21885 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], [], uu____21885, erasable,
                                Prims.int_zero)
                               in
                            FStar_List.fold_left2
                              (fun uu____21967  ->
                                 fun uu____21968  ->
                                   fun x  ->
                                     match (uu____21967, uu____21968) with
                                     | ((env2,bvs,tms,pats,subst,g,erasable1,i),
                                        (p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____22152 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____22152 with
                                          | (bvs_p,tms_p,e_p,p2,g',erasable_p)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____22222 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____22222 i
                                                   in
                                                let uu____22223 =
                                                  let uu____22232 =
                                                    let uu____22237 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    mk_disc_t uu____22237  in
                                                  FStar_List.map uu____22232
                                                   in
                                                FStar_All.pipe_right tms_p
                                                  uu____22223
                                                 in
                                              let uu____22243 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append tms tms_p1),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst),
                                                uu____22243,
                                                (erasable1 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____21853 sub_pats1 simple_bvs1
                             in
                          (match uu____21821 with
                           | (_env,bvs,tms,checked_sub_pats,subst,g,erasable1,uu____22302)
                               ->
                               let pat_e =
                                 FStar_Syntax_Subst.subst subst simple_pat_e1
                                  in
                               let reconstruct_nested_pat pat =
                                 let rec aux simple_pats bvs1 sub_pats2 =
                                   match simple_pats with
                                   | [] -> []
                                   | (hd,b)::simple_pats1 ->
                                       (match hd.FStar_Syntax_Syntax.v with
                                        | FStar_Syntax_Syntax.Pat_dot_term
                                            (x,e) ->
                                            let e1 =
                                              FStar_Syntax_Subst.subst subst
                                                e
                                               in
                                            let hd1 =
                                              let uu___2818_22478 = hd  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2818_22478.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____22483 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd1, b) :: uu____22483
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd1,uu____22527)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____22564 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd1, b) :: uu____22564
                                             | uu____22584 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____22610 ->
                                            failwith
                                              "Impossible: expected a simple pattern")
                                    in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1,simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats
                                        in
                                     let uu___2839_22653 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2839_22653.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____22665 -> failwith "Impossible"  in
                               let uu____22669 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, tms, pat_e, uu____22669, g, erasable1))))))
           in
        (let uu____22676 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____22676
         then
           let uu____22681 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____22681
         else ());
        (let uu____22686 =
           let uu____22704 =
             let uu___2844_22705 =
               let uu____22706 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____22706 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2844_22705.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2844_22705.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2844_22705.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2844_22705.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2844_22705.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2844_22705.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2844_22705.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2844_22705.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2844_22705.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2844_22705.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2844_22705.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2844_22705.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2844_22705.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2844_22705.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2844_22705.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2844_22705.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___2844_22705.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2844_22705.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2844_22705.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2844_22705.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2844_22705.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2844_22705.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2844_22705.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2844_22705.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2844_22705.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2844_22705.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2844_22705.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2844_22705.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2844_22705.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2844_22705.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2844_22705.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2844_22705.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2844_22705.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2844_22705.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2844_22705.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2844_22705.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2844_22705.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2844_22705.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2844_22705.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2844_22705.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2844_22705.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2844_22705.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2844_22705.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2844_22705.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2844_22705.FStar_TypeChecker_Env.erasable_types_tab)
             }  in
           let uu____22722 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____22704 uu____22722 pat_t  in
         match uu____22686 with
         | (bvs,tms,pat_e,pat,g,erasable) ->
             ((let uu____22761 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____22761
               then
                 let uu____22766 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____22768 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____22766
                   uu____22768
               else ());
              (let uu____22773 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____22774 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, tms, uu____22773, pat_e, uu____22774, g, erasable))))

and (tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.branch ->
        ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) *
          FStar_Syntax_Syntax.term * FStar_Ident.lident *
          FStar_Syntax_Syntax.cflag Prims.list *
          (Prims.bool -> FStar_TypeChecker_Common.lcomp) *
          FStar_TypeChecker_Common.guard_t * Prims.bool))
  =
  fun scrutinee  ->
    fun env  ->
      fun branch  ->
        let uu____22812 = FStar_Syntax_Subst.open_branch branch  in
        match uu____22812 with
        | (pattern,when_clause,branch_exp) ->
            let uu____22861 = branch  in
            (match uu____22861 with
             | (cpat,uu____22892,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____22914 =
                   let uu____22921 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____22921
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____22914 with
                  | (scrutinee_env,uu____22958) ->
                      let uu____22963 = tc_pat env pat_t pattern  in
                      (match uu____22963 with
                       | (pattern1,pat_bvs,pat_bv_tms,pat_env,pat_exp,norm_pat_exp,guard_pat,erasable)
                           ->
                           ((let uu____23033 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____23033
                             then
                               let uu____23037 =
                                 FStar_Syntax_Print.pat_to_string pattern1
                                  in
                               let uu____23039 =
                                 FStar_Syntax_Print.bvs_to_string ";" pat_bvs
                                  in
                               let uu____23042 =
                                 FStar_List.fold_left
                                   (fun s  ->
                                      fun t  ->
                                        let uu____23051 =
                                          let uu____23053 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat ";" uu____23053  in
                                        Prims.op_Hat s uu____23051) ""
                                   pat_bv_tms
                                  in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____23037 uu____23039 uu____23042
                             else ());
                            (let uu____23060 =
                               match when_clause with
                               | FStar_Pervasives_Native.None  ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____23090 =
                                     FStar_TypeChecker_Env.should_verify env
                                      in
                                   if uu____23090
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____23113 =
                                        let uu____23120 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool
                                           in
                                        tc_term uu____23120 e  in
                                      match uu____23113 with
                                      | (e1,c,g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g))
                                in
                             match uu____23060 with
                             | (when_clause1,g_when) ->
                                 let uu____23177 = tc_term pat_env branch_exp
                                    in
                                 (match uu____23177 with
                                  | (branch_exp1,c,g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None  ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____23236 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool
                                                 in
                                              FStar_All.pipe_left
                                                (fun uu____23247  ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____23247) uu____23236
                                           in
                                        let branch_guard =
                                          let uu____23251 =
                                            let uu____23253 =
                                              FStar_TypeChecker_Env.should_verify
                                                env
                                               in
                                            Prims.op_Negation uu____23253  in
                                          if uu____23251
                                          then FStar_Syntax_Util.t_true
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____23309 =
                                                   let uu____23317 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v
                                                      in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____23317
                                                    in
                                                 match uu____23309 with
                                                 | (is_induc,datacons) ->
                                                     if
                                                       (Prims.op_Negation
                                                          is_induc)
                                                         ||
                                                         ((FStar_List.length
                                                             datacons)
                                                            > Prims.int_one)
                                                     then
                                                       let discriminator =
                                                         FStar_Syntax_Util.mk_discriminator
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       let uu____23333 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator
                                                          in
                                                       (match uu____23333
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                             -> []
                                                        | uu____23354 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let disc1 =
                                                              let uu____23370
                                                                =
                                                                let uu____23375
                                                                  =
                                                                  let uu____23376
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                  [uu____23376]
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Tm_app
                                                                  disc
                                                                  uu____23375
                                                                 in
                                                              uu____23370
                                                                FStar_Pervasives_Native.None
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____23401 =
                                                              FStar_Syntax_Util.mk_eq2
                                                                FStar_Syntax_Syntax.U_zero
                                                                FStar_Syntax_Util.t_bool
                                                                disc1
                                                                FStar_Syntax_Util.exp_true_bool
                                                               in
                                                            [uu____23401])
                                                     else []
                                                  in
                                               let fail uu____23409 =
                                                 let uu____23410 =
                                                   let uu____23412 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos
                                                      in
                                                   let uu____23414 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1
                                                      in
                                                   let uu____23416 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1
                                                      in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____23412 uu____23414
                                                     uu____23416
                                                    in
                                                 failwith uu____23410  in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1,uu____23431) ->
                                                     head_constructor t1
                                                 | uu____23436 -> fail ()  in
                                               let force_scrutinee
                                                 uu____23442 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____23443 =
                                                       let uu____23445 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p
                                                          in
                                                       let uu____23447 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2
                                                          in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____23445
                                                         uu____23447
                                                        in
                                                     failwith uu____23443
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t
                                                  in
                                               let pat_exp2 =
                                                 let uu____23454 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____23454
                                                   FStar_Syntax_Util.unmeta
                                                  in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____23459,FStar_Syntax_Syntax.Tm_name
                                                  uu____23460) -> []
                                               | (uu____23461,FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit ))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____23464 =
                                                     let uu____23465 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1
                                                        in
                                                     let uu____23466 =
                                                       force_scrutinee ()  in
                                                     FStar_Syntax_Util.mk_eq2
                                                       FStar_Syntax_Syntax.U_zero
                                                       uu____23465
                                                       uu____23466 pat_exp2
                                                      in
                                                   [uu____23464]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____23467,FStar_Pervasives_Native.Some
                                                   uu____23468)),uu____23469)
                                                   ->
                                                   let uu____23486 =
                                                     let uu____23493 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env
                                                        in
                                                     match uu____23493 with
                                                     | (env1,uu____23507) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2
                                                      in
                                                   (match uu____23486 with
                                                    | (uu____23514,t,uu____23516)
                                                        ->
                                                        let uu____23517 =
                                                          let uu____23518 =
                                                            force_scrutinee
                                                              ()
                                                             in
                                                          FStar_Syntax_Util.mk_eq2
                                                            FStar_Syntax_Syntax.U_zero
                                                            t uu____23518
                                                            pat_exp2
                                                           in
                                                        [uu____23517])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____23519,[]),FStar_Syntax_Syntax.Tm_uinst
                                                  uu____23520) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____23544 =
                                                     let uu____23546 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____23546
                                                      in
                                                   if uu____23544
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____23556 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____23559 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____23556
                                                        uu____23559)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____23562,[]),FStar_Syntax_Syntax.Tm_fvar
                                                  uu____23563) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____23581 =
                                                     let uu____23583 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____23583
                                                      in
                                                   if uu____23581
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____23593 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____23596 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____23593
                                                        uu____23596)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____23599,pat_args),FStar_Syntax_Syntax.Tm_app
                                                  (head,args)) ->
                                                   let f =
                                                     head_constructor head
                                                      in
                                                   let uu____23646 =
                                                     (let uu____23650 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      Prims.op_Negation
                                                        uu____23650)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args))
                                                      in
                                                   if uu____23646
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____23678 =
                                                          let uu____23683 =
                                                            FStar_List.zip
                                                              pat_args args
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____23683
                                                            (FStar_List.mapi
                                                               (fun i  ->
                                                                  fun
                                                                    uu____23769
                                                                     ->
                                                                    match uu____23769
                                                                    with
                                                                    | 
                                                                    ((pi,uu____23791),
                                                                    (ei,uu____23793))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____23821
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____23821
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____23842
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____23854
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____23854
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____23856
                                                                    =
                                                                    let uu____23857
                                                                    =
                                                                    let uu____23862
                                                                    =
                                                                    let uu____23863
                                                                    =
                                                                    let uu____23872
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____23872
                                                                     in
                                                                    [uu____23863]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____23862
                                                                     in
                                                                    uu____23857
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____23856
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____23678
                                                          FStar_List.flatten
                                                         in
                                                      let uu____23895 =
                                                        let uu____23898 =
                                                          force_scrutinee ()
                                                           in
                                                        discriminate
                                                          uu____23898 f
                                                         in
                                                      FStar_List.append
                                                        uu____23895
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____23901,uu____23902) ->
                                                   []
                                               | uu____23909 ->
                                                   let uu____23914 =
                                                     let uu____23916 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2
                                                        in
                                                     let uu____23918 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2
                                                        in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____23916
                                                       uu____23918
                                                      in
                                                   failwith uu____23914
                                                in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____23947 =
                                                 let uu____23949 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____23949
                                                  in
                                               if uu____23947
                                               then
                                                 FStar_TypeChecker_Util.fvar_const
                                                   env
                                                   FStar_Parser_Const.true_lid
                                               else
                                                 (let t =
                                                    let uu____23955 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_conj_l
                                                      uu____23955
                                                     in
                                                  let uu____23964 =
                                                    FStar_Syntax_Util.type_u
                                                      ()
                                                     in
                                                  match uu____23964 with
                                                  | (k,uu____23970) ->
                                                      let uu____23971 =
                                                        tc_check_tot_or_gtot_term
                                                          scrutinee_env t k
                                                          ""
                                                         in
                                                      (match uu____23971 with
                                                       | (t1,uu____23980,uu____23981)
                                                           -> t1))
                                                in
                                             let branch_guard =
                                               build_and_check_branch_guard
                                                 (FStar_Pervasives_Native.Some
                                                    scrutinee_tm) pattern1
                                                 norm_pat_exp
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
                                        let uu____23995 =
                                          let eqs =
                                            let uu____24015 =
                                              let uu____24017 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____24017
                                               in
                                            if uu____24015
                                            then FStar_Pervasives_Native.None
                                            else
                                              (let e =
                                                 FStar_Syntax_Subst.compress
                                                   pat_exp
                                                  in
                                               match e.FStar_Syntax_Syntax.n
                                               with
                                               | FStar_Syntax_Syntax.Tm_uvar
                                                   uu____24027 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_constant
                                                   uu____24040 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_fvar
                                                   uu____24041 ->
                                                   FStar_Pervasives_Native.None
                                               | uu____24042 ->
                                                   let uu____24043 =
                                                     let uu____24044 =
                                                       env.FStar_TypeChecker_Env.universe_of
                                                         env pat_t
                                                        in
                                                     FStar_Syntax_Util.mk_eq2
                                                       uu____24044 pat_t
                                                       scrutinee_tm e
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____24043)
                                             in
                                          let uu____24045 =
                                            FStar_TypeChecker_Util.strengthen_precondition
                                              FStar_Pervasives_Native.None
                                              env branch_exp1 c g_branch
                                             in
                                          match uu____24045 with
                                          | (c1,g_branch1) ->
                                              let branch_has_layered_effect =
                                                let uu____24074 =
                                                  FStar_All.pipe_right
                                                    c1.FStar_TypeChecker_Common.eff_name
                                                    (FStar_TypeChecker_Env.norm_eff_name
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____24074
                                                  (FStar_TypeChecker_Env.is_layered_effect
                                                     env)
                                                 in
                                              let uu____24076 =
                                                let env1 =
                                                  let uu____24082 =
                                                    FStar_All.pipe_right
                                                      pat_bvs
                                                      (FStar_List.map
                                                         FStar_Syntax_Syntax.mk_binder)
                                                     in
                                                  FStar_TypeChecker_Env.push_binders
                                                    scrutinee_env uu____24082
                                                   in
                                                if branch_has_layered_effect
                                                then
                                                  let c2 =
                                                    FStar_TypeChecker_Util.weaken_precondition
                                                      env1 c1
                                                      (FStar_TypeChecker_Common.NonTrivial
                                                         branch_guard)
                                                     in
                                                  (c2,
                                                    FStar_TypeChecker_Env.trivial_guard)
                                                else
                                                  (match (eqs,
                                                           when_condition)
                                                   with
                                                   | uu____24103 when
                                                       let uu____24114 =
                                                         FStar_TypeChecker_Env.should_verify
                                                           env1
                                                          in
                                                       Prims.op_Negation
                                                         uu____24114
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
                                                         FStar_TypeChecker_Env.guard_of_guard_formula
                                                           gf
                                                          in
                                                       let uu____24135 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 gf
                                                          in
                                                       let uu____24136 =
                                                         FStar_TypeChecker_Env.imp_guard
                                                           g g_when
                                                          in
                                                       (uu____24135,
                                                         uu____24136)
                                                   | (FStar_Pervasives_Native.Some
                                                      f,FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_f =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           f
                                                          in
                                                       let g_fw =
                                                         let uu____24151 =
                                                           FStar_Syntax_Util.mk_conj
                                                             f w
                                                            in
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           uu____24151
                                                          in
                                                       let uu____24152 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_fw
                                                          in
                                                       let uu____24153 =
                                                         let uu____24154 =
                                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                                             g_f
                                                            in
                                                         FStar_TypeChecker_Env.imp_guard
                                                           uu____24154 g_when
                                                          in
                                                       (uu____24152,
                                                         uu____24153)
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_w =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           w
                                                          in
                                                       let g =
                                                         FStar_TypeChecker_Env.guard_of_guard_formula
                                                           g_w
                                                          in
                                                       let uu____24168 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_w
                                                          in
                                                       (uu____24168, g_when))
                                                 in
                                              (match uu____24076 with
                                               | (c_weak,g_when_weak) ->
                                                   let binders =
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder
                                                       pat_bvs
                                                      in
                                                   let maybe_return_c_weak
                                                     should_return =
                                                     let c_weak1 =
                                                       let uu____24211 =
                                                         should_return &&
                                                           (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                              c_weak)
                                                          in
                                                       if uu____24211
                                                       then
                                                         FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                           env branch_exp1
                                                           c_weak
                                                       else c_weak  in
                                                     if
                                                       branch_has_layered_effect
                                                     then
                                                       ((let uu____24218 =
                                                           FStar_All.pipe_left
                                                             (FStar_TypeChecker_Env.debug
                                                                env)
                                                             (FStar_Options.Other
                                                                "LayeredEffects")
                                                            in
                                                         if uu____24218
                                                         then
                                                           FStar_Util.print_string
                                                             "Typechecking pat_bv_tms ...\n"
                                                         else ());
                                                        (let pat_bv_tms1 =
                                                           FStar_All.pipe_right
                                                             pat_bv_tms
                                                             (FStar_List.map
                                                                (fun
                                                                   pat_bv_tm 
                                                                   ->
                                                                   let uu____24238
                                                                    =
                                                                    let uu____24243
                                                                    =
                                                                    let uu____24244
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____24244]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____24243
                                                                     in
                                                                   uu____24238
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange))
                                                            in
                                                         let pat_bv_tms2 =
                                                           let env1 =
                                                             let uu___3084_24281
                                                               =
                                                               FStar_TypeChecker_Env.push_bv
                                                                 env
                                                                 scrutinee
                                                                in
                                                             {
                                                               FStar_TypeChecker_Env.solver
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.solver);
                                                               FStar_TypeChecker_Env.range
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.range);
                                                               FStar_TypeChecker_Env.curmodule
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.curmodule);
                                                               FStar_TypeChecker_Env.gamma
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.gamma);
                                                               FStar_TypeChecker_Env.gamma_sig
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.gamma_sig);
                                                               FStar_TypeChecker_Env.gamma_cache
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.gamma_cache);
                                                               FStar_TypeChecker_Env.modules
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.modules);
                                                               FStar_TypeChecker_Env.expected_typ
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.expected_typ);
                                                               FStar_TypeChecker_Env.sigtab
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.sigtab);
                                                               FStar_TypeChecker_Env.attrtab
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.attrtab);
                                                               FStar_TypeChecker_Env.instantiate_imp
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.instantiate_imp);
                                                               FStar_TypeChecker_Env.effects
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.effects);
                                                               FStar_TypeChecker_Env.generalize
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.generalize);
                                                               FStar_TypeChecker_Env.letrecs
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.letrecs);
                                                               FStar_TypeChecker_Env.top_level
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.top_level);
                                                               FStar_TypeChecker_Env.check_uvars
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.check_uvars);
                                                               FStar_TypeChecker_Env.use_eq
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.use_eq);
                                                               FStar_TypeChecker_Env.use_eq_strict
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.use_eq_strict);
                                                               FStar_TypeChecker_Env.is_iface
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.is_iface);
                                                               FStar_TypeChecker_Env.admit
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.admit);
                                                               FStar_TypeChecker_Env.lax
                                                                 = true;
                                                               FStar_TypeChecker_Env.lax_universes
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.lax_universes);
                                                               FStar_TypeChecker_Env.phase1
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.phase1);
                                                               FStar_TypeChecker_Env.failhard
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.failhard);
                                                               FStar_TypeChecker_Env.nosynth
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.nosynth);
                                                               FStar_TypeChecker_Env.uvar_subtyping
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.uvar_subtyping);
                                                               FStar_TypeChecker_Env.tc_term
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.tc_term);
                                                               FStar_TypeChecker_Env.type_of
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.type_of);
                                                               FStar_TypeChecker_Env.universe_of
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.universe_of);
                                                               FStar_TypeChecker_Env.check_type_of
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.check_type_of);
                                                               FStar_TypeChecker_Env.use_bv_sorts
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.use_bv_sorts);
                                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                               FStar_TypeChecker_Env.normalized_eff_names
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.normalized_eff_names);
                                                               FStar_TypeChecker_Env.fv_delta_depths
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.fv_delta_depths);
                                                               FStar_TypeChecker_Env.proof_ns
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.proof_ns);
                                                               FStar_TypeChecker_Env.synth_hook
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.synth_hook);
                                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                               FStar_TypeChecker_Env.splice
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.splice);
                                                               FStar_TypeChecker_Env.mpreprocess
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.mpreprocess);
                                                               FStar_TypeChecker_Env.postprocess
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.postprocess);
                                                               FStar_TypeChecker_Env.identifier_info
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.identifier_info);
                                                               FStar_TypeChecker_Env.tc_hooks
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.tc_hooks);
                                                               FStar_TypeChecker_Env.dsenv
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.dsenv);
                                                               FStar_TypeChecker_Env.nbe
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.nbe);
                                                               FStar_TypeChecker_Env.strict_args_tab
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.strict_args_tab);
                                                               FStar_TypeChecker_Env.erasable_types_tab
                                                                 =
                                                                 (uu___3084_24281.FStar_TypeChecker_Env.erasable_types_tab)
                                                             }  in
                                                           let uu____24283 =
                                                             let uu____24286
                                                               =
                                                               FStar_List.fold_left2
                                                                 (fun
                                                                    uu____24314
                                                                     ->
                                                                    fun
                                                                    pat_bv_tm
                                                                     ->
                                                                    fun bv 
                                                                    ->
                                                                    match uu____24314
                                                                    with
                                                                    | 
                                                                    (substs,acc)
                                                                    ->
                                                                    let expected_t
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    substs
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    let pat_bv_tm1
                                                                    =
                                                                    let uu____24355
                                                                    =
                                                                    let uu____24362
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pat_bv_tm
                                                                    (FStar_Syntax_Subst.subst
                                                                    substs)
                                                                     in
                                                                    let uu____24363
                                                                    =
                                                                    let uu____24374
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t
                                                                     in
                                                                    tc_trivial_guard
                                                                    uu____24374
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24362
                                                                    uu____24363
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24355
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    ((FStar_List.append
                                                                    substs
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv,
                                                                    pat_bv_tm1)]),
                                                                    (FStar_List.append
                                                                    acc
                                                                    [pat_bv_tm1])))
                                                                 ([], [])
                                                                 pat_bv_tms1
                                                                 pat_bvs
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____24286
                                                               FStar_Pervasives_Native.snd
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____24283
                                                             (FStar_List.map
                                                                (FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Env.Beta]
                                                                   env1))
                                                            in
                                                         (let uu____24436 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects")
                                                             in
                                                          if uu____24436
                                                          then
                                                            let uu____24441 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____24450
                                                                    =
                                                                    let uu____24452
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____24452
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____24450)
                                                                ""
                                                                pat_bv_tms2
                                                               in
                                                            let uu____24456 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____24465
                                                                    =
                                                                    let uu____24467
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____24467
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____24465)
                                                                "" pat_bvs
                                                               in
                                                            FStar_Util.print2
                                                              "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                                                              uu____24441
                                                              uu____24456
                                                          else ());
                                                         (let uu____24474 =
                                                            FStar_All.pipe_right
                                                              c_weak1
                                                              (FStar_TypeChecker_Common.apply_lcomp
                                                                 (fun c2  ->
                                                                    c2)
                                                                 (fun g  ->
                                                                    match eqs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> g
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    eqs1 ->
                                                                    FStar_TypeChecker_Common.weaken_guard_formula
                                                                    g eqs1))
                                                             in
                                                          let uu____24481 =
                                                            let uu____24486 =
                                                              FStar_TypeChecker_Env.push_bv
                                                                env scrutinee
                                                               in
                                                            FStar_TypeChecker_Util.close_layered_lcomp
                                                              uu____24486
                                                              pat_bvs
                                                              pat_bv_tms2
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____24474
                                                            uu____24481)))
                                                     else
                                                       FStar_TypeChecker_Util.close_wp_lcomp
                                                         env pat_bvs c_weak1
                                                      in
                                                   let uu____24489 =
                                                     FStar_TypeChecker_Env.close_guard
                                                       env binders
                                                       g_when_weak
                                                      in
                                                   let uu____24490 =
                                                     FStar_TypeChecker_Env.conj_guard
                                                       guard_pat g_branch1
                                                      in
                                                   ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                     (c_weak.FStar_TypeChecker_Common.cflags),
                                                     maybe_return_c_weak,
                                                     uu____24489,
                                                     uu____24490))
                                           in
                                        match uu____23995 with
                                        | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                            ->
                                            let guard =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_when1 g_branch1
                                               in
                                            ((let uu____24545 =
                                                FStar_TypeChecker_Env.debug
                                                  env FStar_Options.High
                                                 in
                                              if uu____24545
                                              then
                                                let uu____24548 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____24548
                                              else ());
                                             (let uu____24554 =
                                                FStar_Syntax_Subst.close_branch
                                                  (pattern1, when_clause1,
                                                    branch_exp1)
                                                 in
                                              let uu____24571 =
                                                let uu____24572 =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs
                                                   in
                                                FStar_TypeChecker_Util.close_guard_implicits
                                                  env false uu____24572 guard
                                                 in
                                              (uu____24554, branch_guard,
                                                effect_label, cflags,
                                                maybe_return_c, uu____24571,
                                                erasable)))))))))))

and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____24621 = check_let_bound_def true env1 lb  in
          (match uu____24621 with
           | (e1,univ_vars,c1,g1,annotated) ->
               let uu____24647 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24669 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____24669, univ_vars, c1)
                 else
                   (let g11 =
                      let uu____24675 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____24675
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____24676 = FStar_TypeChecker_Common.lcomp_comp c1
                       in
                    match uu____24676 with
                    | (comp1,g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1  in
                        let uu____24694 =
                          let uu____24707 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)]
                             in
                          FStar_List.hd uu____24707  in
                        (match uu____24694 with
                         | (uu____24757,univs,e11,c11,gvs) ->
                             let g13 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.map_guard g12)
                                 (FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta;
                                    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                    FStar_TypeChecker_Env.CompressUvars;
                                    FStar_TypeChecker_Env.NoFullNorm;
                                    FStar_TypeChecker_Env.Exclude
                                      FStar_TypeChecker_Env.Zeta] env1)
                                in
                             let g14 =
                               FStar_TypeChecker_Env.abstract_guard_n gvs g13
                                in
                             let uu____24771 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11  in
                             (g14, e11, univs, uu____24771)))
                  in
               (match uu____24647 with
                | (g11,e11,univ_vars1,c11) ->
                    let uu____24788 =
                      let uu____24797 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____24797
                      then
                        let uu____24808 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____24808 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____24842 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____24842
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____24843 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____24843, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____24855 =
                            FStar_TypeChecker_Common.lcomp_comp c11  in
                          match uu____24855 with
                          | (comp1,g_comp1) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env1
                                 g_comp1;
                               (let c =
                                  FStar_All.pipe_right comp1
                                    (FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Env.Beta;
                                       FStar_TypeChecker_Env.NoFullNorm;
                                       FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                       env1)
                                   in
                                let e21 =
                                  let uu____24879 =
                                    FStar_Syntax_Util.is_pure_comp c  in
                                  if uu____24879
                                  then e2
                                  else
                                    ((let uu____24887 =
                                        FStar_TypeChecker_Env.get_range env1
                                         in
                                      FStar_Errors.log_issue uu____24887
                                        FStar_TypeChecker_Err.top_level_effect);
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Masked_effect)))
                                       FStar_Pervasives_Native.None
                                       e2.FStar_Syntax_Syntax.pos)
                                   in
                                (e21, c)))))
                       in
                    (match uu____24788 with
                     | (e21,c12) ->
                         ((let uu____24911 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____24911
                           then
                             let uu____24914 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____24914
                           else ());
                          (let e12 =
                             let uu____24920 = FStar_Options.tcnorm ()  in
                             if uu____24920
                             then
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.UnfoldAttr
                                    [FStar_Parser_Const.tcnorm_attr];
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1 e11
                             else e11  in
                           (let uu____24926 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____24926
                            then
                              let uu____24929 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____24929
                            else ());
                           (let cres =
                              let uu____24935 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12
                                 in
                              if uu____24935
                              then
                                FStar_Syntax_Syntax.mk_Total'
                                  FStar_Syntax_Syntax.t_unit
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.U_zero)
                              else
                                (let c1_comp_typ =
                                   FStar_All.pipe_right c12
                                     (FStar_TypeChecker_Env.unfold_effect_abbrev
                                        env1)
                                    in
                                 let c1_wp =
                                   match c1_comp_typ.FStar_Syntax_Syntax.effect_args
                                   with
                                   | (wp,uu____24943)::[] -> wp
                                   | uu____24968 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args"
                                    in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name
                                    in
                                 let wp2 =
                                   let ret =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_return_vc_combinator
                                      in
                                   let uu____24985 =
                                     let uu____24990 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [FStar_Syntax_Syntax.U_zero] env1
                                         c1_eff_decl ret
                                        in
                                     let uu____24991 =
                                       let uu____24992 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.t_unit
                                          in
                                       let uu____25001 =
                                         let uu____25012 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.unit_const
                                            in
                                         [uu____25012]  in
                                       uu____24992 :: uu____25001  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24990 uu____24991
                                      in
                                   uu____24985 FStar_Pervasives_Native.None
                                     e21.FStar_Syntax_Syntax.pos
                                    in
                                 let wp =
                                   let bind =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator
                                      in
                                   let uu____25049 =
                                     let uu____25054 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         (FStar_List.append
                                            c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                            [FStar_Syntax_Syntax.U_zero])
                                         env1 c1_eff_decl bind
                                        in
                                     let uu____25055 =
                                       let uu____25056 =
                                         let uu____25065 =
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_constant
                                                (FStar_Const.Const_range
                                                   (lb.FStar_Syntax_Syntax.lbpos)))
                                             FStar_Pervasives_Native.None
                                             lb.FStar_Syntax_Syntax.lbpos
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____25065
                                          in
                                       let uu____25074 =
                                         let uu____25085 =
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                            in
                                         let uu____25102 =
                                           let uu____25113 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.t_unit
                                              in
                                           let uu____25122 =
                                             let uu____25133 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c1_wp
                                                in
                                             let uu____25142 =
                                               let uu____25153 =
                                                 let uu____25162 =
                                                   let uu____25163 =
                                                     let uu____25164 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                                        in
                                                     [uu____25164]  in
                                                   FStar_Syntax_Util.abs
                                                     uu____25163 wp2
                                                     (FStar_Pervasives_Native.Some
                                                        (FStar_Syntax_Util.mk_residual_comp
                                                           FStar_Parser_Const.effect_Tot_lid
                                                           FStar_Pervasives_Native.None
                                                           [FStar_Syntax_Syntax.TOTAL]))
                                                    in
                                                 FStar_All.pipe_left
                                                   FStar_Syntax_Syntax.as_arg
                                                   uu____25162
                                                  in
                                               [uu____25153]  in
                                             uu____25133 :: uu____25142  in
                                           uu____25113 :: uu____25122  in
                                         uu____25085 :: uu____25102  in
                                       uu____25056 :: uu____25074  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____25054 uu____25055
                                      in
                                   uu____25049 FStar_Pervasives_Native.None
                                     lb.FStar_Syntax_Syntax.lbpos
                                    in
                                 let uu____25241 =
                                   let uu____25242 =
                                     let uu____25253 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____25253]  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____25242;
                                     FStar_Syntax_Syntax.flags = []
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____25241)
                               in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars1
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos
                               in
                            let uu____25281 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____25295 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres  in
                            (uu____25281, uu____25295,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____25296 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____25307 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____25307
        then
          let universe_of_binders bs =
            let uu____25334 =
              FStar_List.fold_left
                (fun uu____25359  ->
                   fun b  ->
                     match uu____25359 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____25334 with | (uu____25407,us) -> FStar_List.rev us
             in
          let quant =
            FStar_Syntax_Util.smt_lemma_as_forall lem_typ universe_of_binders
             in
          FStar_TypeChecker_Util.weaken_precondition env c2
            (FStar_TypeChecker_Common.NonTrivial quant)
        else c2

and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___3216_25443 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3216_25443.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3216_25443.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3216_25443.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3216_25443.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3216_25443.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3216_25443.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3216_25443.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3216_25443.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3216_25443.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3216_25443.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3216_25443.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3216_25443.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3216_25443.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3216_25443.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3216_25443.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3216_25443.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___3216_25443.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___3216_25443.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3216_25443.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3216_25443.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3216_25443.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3216_25443.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3216_25443.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3216_25443.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3216_25443.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3216_25443.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3216_25443.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3216_25443.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3216_25443.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3216_25443.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3216_25443.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3216_25443.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3216_25443.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3216_25443.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3216_25443.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3216_25443.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3216_25443.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3216_25443.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3216_25443.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3216_25443.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3216_25443.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3216_25443.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3216_25443.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3216_25443.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3216_25443.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____25445 =
            let uu____25457 =
              let uu____25458 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____25458 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____25457 lb  in
          (match uu____25445 with
           | (e1,uu____25481,c1,g1,annotated) ->
               let pure_or_ghost =
                 FStar_TypeChecker_Common.is_pure_or_ghost_lcomp c1  in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs
                  in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____25495 =
                     let uu____25501 =
                       let uu____25503 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____25505 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____25503 uu____25505
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____25501)
                      in
                   FStar_Errors.raise_error uu____25495
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____25516 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ)
                      in
                   if uu____25516
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___3231_25528 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3231_25528.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3231_25528.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   }  in
                 let uu____25529 =
                   let uu____25534 =
                     let uu____25535 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____25535]  in
                   FStar_Syntax_Subst.open_term uu____25534 e2  in
                 match uu____25529 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____25579 =
                       let uu____25586 = tc_term env_x e21  in
                       FStar_All.pipe_right uu____25586
                         (fun uu____25612  ->
                            match uu____25612 with
                            | (e22,c2,g2) ->
                                let uu____25628 =
                                  let uu____25633 =
                                    FStar_All.pipe_right
                                      (fun uu____25651  ->
                                         "folding guard g2 of e2 in the lcomp")
                                      (fun uu____25657  ->
                                         FStar_Pervasives_Native.Some
                                           uu____25657)
                                     in
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    uu____25633 env_x e22 c2 g2
                                   in
                                (match uu____25628 with
                                 | (c21,g21) -> (e22, c21, g21)))
                        in
                     (match uu____25579 with
                      | (e22,c2,g2) ->
                          let c21 =
                            maybe_intro_smt_lemma env_x
                              c1.FStar_TypeChecker_Common.res_typ c2
                             in
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c21)
                             in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ
                             in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c21.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c21.FStar_TypeChecker_Common.res_typ
                             in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_TypeChecker_Common.res_typ
                              cres.FStar_TypeChecker_Common.eff_name e11
                              attrs lb.FStar_Syntax_Syntax.lbpos
                             in
                          let e3 =
                            let uu____25685 =
                              let uu____25692 =
                                let uu____25693 =
                                  let uu____25707 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____25707)  in
                                FStar_Syntax_Syntax.Tm_let uu____25693  in
                              FStar_Syntax_Syntax.mk uu____25692  in
                            uu____25685 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ
                             in
                          let g21 =
                            let uu____25725 =
                              let uu____25727 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2)
                                 in
                              FStar_All.pipe_right uu____25727
                                (FStar_TypeChecker_Env.is_layered_effect env2)
                               in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____25725 xb g2
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g21
                             in
                          let uu____25730 =
                            let uu____25732 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____25732  in
                          if uu____25730
                          then
                            let tt =
                              let uu____25743 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____25743
                                FStar_Option.get
                               in
                            ((let uu____25749 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____25749
                              then
                                let uu____25754 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____25756 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____25754 uu____25756
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____25763 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ
                                in
                             match uu____25763 with
                             | (t,g_ex) ->
                                 ((let uu____25777 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____25777
                                   then
                                     let uu____25782 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ
                                        in
                                     let uu____25784 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____25782 uu____25784
                                   else ());
                                  (let uu____25789 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___3270_25791 = cres  in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3270_25791.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3270_25791.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3270_25791.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____25789))))))))
      | uu____25792 ->
          failwith "Impossible (inner let with more than one lb)"

and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____25828 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25828 with
           | (lbs1,e21) ->
               let uu____25847 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25847 with
                | (env0,topt) ->
                    let uu____25866 = build_let_rec_env true env0 lbs1  in
                    (match uu____25866 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25889 = check_let_recs rec_env lbs2  in
                         (match uu____25889 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____25909 =
                                  let uu____25910 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____25910
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____25909
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____25916 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____25916
                                  (fun uu____25933  ->
                                     FStar_Pervasives_Native.Some uu____25933)
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
                                              lbdef
                                              lb.FStar_Syntax_Syntax.lbattrs
                                              lb.FStar_Syntax_Syntax.lbpos))
                                else
                                  (let ecs =
                                     let uu____25970 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____26004 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____26004)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____25970
                                      in
                                   FStar_List.map2
                                     (fun uu____26039  ->
                                        fun lb  ->
                                          match uu____26039 with
                                          | (x,uvs,e,c,gvs) ->
                                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                all_lb_names x uvs
                                                (FStar_Syntax_Util.comp_result
                                                   c)
                                                (FStar_Syntax_Util.comp_effect_name
                                                   c) e
                                                lb.FStar_Syntax_Syntax.lbattrs
                                                lb.FStar_Syntax_Syntax.lbpos)
                                     ecs lbs3)
                                 in
                              let cres =
                                let uu____26087 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____26087
                                 in
                              let uu____26088 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____26088 with
                               | (lbs5,e22) ->
                                   ((let uu____26108 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____26108
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____26109 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____26109, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____26123 -> failwith "Impossible"

and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____26159 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____26159 with
           | (lbs1,e21) ->
               let uu____26178 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____26178 with
                | (env0,topt) ->
                    let uu____26197 = build_let_rec_env false env0 lbs1  in
                    (match uu____26197 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____26220 =
                           let uu____26227 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____26227
                             (fun uu____26250  ->
                                match uu____26250 with
                                | (lbs3,g) ->
                                    let uu____26269 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____26269))
                            in
                         (match uu____26220 with
                          | (lbs3,g_lbs) ->
                              let uu____26284 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3345_26307 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3345_26307.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3345_26307.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3348_26309 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3348_26309.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3348_26309.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3348_26309.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3348_26309.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3348_26309.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3348_26309.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____26284 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____26336 = tc_term env2 e21  in
                                   (match uu____26336 with
                                    | (e22,cres,g2) ->
                                        let cres1 =
                                          FStar_List.fold_right
                                            (fun lb  ->
                                               fun cres1  ->
                                                 maybe_intro_smt_lemma env2
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                   cres1) lbs4 cres
                                           in
                                        let cres2 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres1
                                           in
                                        let cres3 =
                                          FStar_TypeChecker_Common.lcomp_set_flags
                                            cres2
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                                           in
                                        let guard =
                                          let uu____26360 =
                                            let uu____26361 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____26361 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____26360
                                           in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_wp_lcomp
                                            env2 bvs cres3
                                           in
                                        let tres =
                                          norm env2
                                            cres4.FStar_TypeChecker_Common.res_typ
                                           in
                                        let cres5 =
                                          let uu___3369_26371 = cres4  in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3369_26371.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3369_26371.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3369_26371.FStar_TypeChecker_Common.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____26379 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____26379))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard
                                           in
                                        let uu____26381 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____26381 with
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
                                                  uu____26422 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____26423 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____26423 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3385_26437
                                                           = cres5  in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3385_26437.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3385_26437.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3385_26437.FStar_TypeChecker_Common.comp_thunk)
                                                         }  in
                                                       let uu____26438 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____26438))))))))))
      | uu____26439 -> failwith "Impossible"

and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Common.guard_t))
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____26487 = FStar_Options.ml_ish ()  in
          if uu____26487
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____26495 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____26495 with
             | (formals,c) ->
                 let uu____26503 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____26503 with
                  | (actuals,uu____26514,uu____26515) ->
                      if
                        ((FStar_List.length formals) < Prims.int_one) ||
                          ((FStar_List.length actuals) < Prims.int_one)
                      then
                        let uu____26536 =
                          let uu____26542 =
                            let uu____26544 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____26546 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____26544 uu____26546
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____26542)
                           in
                        FStar_Errors.raise_error uu____26536
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____26554 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____26554 actuals
                            in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n = FStar_List.length actuals1  in
                              if n = Prims.int_one
                              then "1 argument was found"
                              else
                                (let uu____26585 = FStar_Util.string_of_int n
                                    in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____26585)
                               in
                            let formals_msg =
                              let n = FStar_List.length formals  in
                              if n = Prims.int_one
                              then "1 argument"
                              else
                                (let uu____26604 = FStar_Util.string_of_int n
                                    in
                                 FStar_Util.format1 "%s arguments"
                                   uu____26604)
                               in
                            let msg =
                              let uu____26609 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____26611 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____26609 uu____26611 formals_msg
                                actuals_msg
                               in
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_LetRecArgumentMismatch,
                                msg) lbdef.FStar_Syntax_Syntax.pos)
                         else ();
                         (let quals =
                            FStar_TypeChecker_Env.lookup_effect_quals env
                              (FStar_Syntax_Util.comp_effect_name c)
                             in
                          FStar_All.pipe_right quals
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect)))))
           in
        let uu____26623 =
          FStar_List.fold_left
            (fun uu____26656  ->
               fun lb  ->
                 match uu____26656 with
                 | (lbs1,env1,g_acc) ->
                     let uu____26681 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____26681 with
                      | (univ_vars,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____26704 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars
                                  in
                               let uu____26723 =
                                 let uu____26730 =
                                   let uu____26731 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____26731
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3431_26742 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3431_26742.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3431_26742.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3431_26742.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3431_26742.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3431_26742.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3431_26742.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3431_26742.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3431_26742.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3431_26742.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3431_26742.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3431_26742.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3431_26742.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3431_26742.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3431_26742.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3431_26742.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3431_26742.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___3431_26742.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3431_26742.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3431_26742.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3431_26742.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3431_26742.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3431_26742.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3431_26742.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3431_26742.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3431_26742.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3431_26742.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3431_26742.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3431_26742.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3431_26742.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3431_26742.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3431_26742.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3431_26742.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3431_26742.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3431_26742.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3431_26742.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3431_26742.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3431_26742.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3431_26742.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3431_26742.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3431_26742.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3431_26742.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3431_26742.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3431_26742.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3431_26742.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3431_26742.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) t uu____26730 ""
                                  in
                               match uu____26723 with
                               | (t1,uu____26752,g) ->
                                   let uu____26754 =
                                     let uu____26755 =
                                       let uu____26756 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____26756
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____26755
                                      in
                                   let uu____26757 = norm env01 t1  in
                                   (uu____26754, uu____26757))
                             in
                          (match uu____26704 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____26777 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____26777
                                 then
                                   let uu___3441_26780 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3441_26780.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3441_26780.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3441_26780.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3441_26780.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3441_26780.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3441_26780.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3441_26780.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3441_26780.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3441_26780.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3441_26780.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3441_26780.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3441_26780.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3441_26780.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3441_26780.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3441_26780.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3441_26780.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___3441_26780.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3441_26780.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3441_26780.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3441_26780.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3441_26780.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3441_26780.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3441_26780.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3441_26780.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3441_26780.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3441_26780.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3441_26780.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3441_26780.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3441_26780.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3441_26780.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3441_26780.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3441_26780.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3441_26780.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3441_26780.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3441_26780.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___3441_26780.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3441_26780.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___3441_26780.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3441_26780.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3441_26780.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3441_26780.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3441_26780.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3441_26780.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___3441_26780.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___3441_26780.FStar_TypeChecker_Env.erasable_types_tab)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars, t1)
                                  in
                               let lb1 =
                                 let uu___3444_26794 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3444_26794.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3444_26794.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3444_26794.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3444_26794.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____26623 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____26820 =
        let uu____26829 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____26855 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____26855 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____26885 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____26885
                       | uu____26892 ->
                           let lb1 =
                             let uu___3461_26895 = lb  in
                             let uu____26896 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3461_26895.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3461_26895.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3461_26895.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3461_26895.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____26896;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3461_26895.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3461_26895.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____26899 =
                             let uu____26906 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____26906
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____26899 with
                            | (e,c,g) ->
                                ((let uu____26915 =
                                    let uu____26917 =
                                      FStar_TypeChecker_Common.is_total_lcomp
                                        c
                                       in
                                    Prims.op_Negation uu____26917  in
                                  if uu____26915
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_UnexpectedGTotForLetRec,
                                        "Expected let rec to be a Tot term; got effect GTot")
                                      e.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let lb2 =
                                    FStar_Syntax_Util.mk_letbinding
                                      lb1.FStar_Syntax_Syntax.lbname
                                      lb1.FStar_Syntax_Syntax.lbunivs
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                      FStar_Parser_Const.effect_Tot_lid e
                                      lb1.FStar_Syntax_Syntax.lbattrs
                                      lb1.FStar_Syntax_Syntax.lbpos
                                     in
                                  (lb2, g)))))))
           in
        FStar_All.pipe_right uu____26829 FStar_List.unzip  in
      match uu____26820 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs
              FStar_TypeChecker_Env.trivial_guard
             in
          (lbs1, g_lbs)

and (check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names *
          FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t *
          Prims.bool))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____26973 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____26973 with
        | (env1,uu____26992) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____27000 = check_lbtyp top_level env lb  in
            (match uu____27000 with
             | (topt,wf_annot,univ_vars,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____27049 =
                     tc_maybe_toplevel_term
                       (let uu___3492_27058 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3492_27058.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3492_27058.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3492_27058.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3492_27058.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3492_27058.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3492_27058.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3492_27058.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3492_27058.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3492_27058.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3492_27058.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3492_27058.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3492_27058.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3492_27058.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3492_27058.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3492_27058.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3492_27058.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___3492_27058.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3492_27058.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3492_27058.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3492_27058.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3492_27058.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3492_27058.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3492_27058.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3492_27058.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3492_27058.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3492_27058.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3492_27058.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3492_27058.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3492_27058.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3492_27058.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3492_27058.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3492_27058.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3492_27058.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3492_27058.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3492_27058.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3492_27058.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3492_27058.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3492_27058.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3492_27058.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3492_27058.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3492_27058.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3492_27058.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3492_27058.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3492_27058.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3492_27058.FStar_TypeChecker_Env.erasable_types_tab)
                        }) e11
                      in
                   match uu____27049 with
                   | (e12,c1,g1) ->
                       let uu____27073 =
                         let uu____27078 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____27084  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____27078 e12 c1 wf_annot
                          in
                       (match uu____27073 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____27101 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____27101
                              then
                                let uu____27104 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____27106 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11
                                   in
                                let uu____27108 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____27104 uu____27106 uu____27108
                              else ());
                             (e12, univ_vars, c11, g11,
                               (FStar_Option.isSome topt)))))))

and (check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.subst_elt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____27147 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____27147 with
             | (univ_opening,univ_vars) ->
                 let uu____27180 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars,
                   univ_opening, uu____27180))
        | uu____27185 ->
            let uu____27186 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____27186 with
             | (univ_opening,univ_vars) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____27236 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars,
                     univ_opening, uu____27236)
                 else
                   (let uu____27243 = FStar_Syntax_Util.type_u ()  in
                    match uu____27243 with
                    | (k,uu____27263) ->
                        let uu____27264 =
                          tc_check_tot_or_gtot_term env1 t1 k ""  in
                        (match uu____27264 with
                         | (t2,uu____27287,g) ->
                             ((let uu____27290 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____27290
                               then
                                 let uu____27293 =
                                   let uu____27295 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____27295
                                    in
                                 let uu____27296 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____27293 uu____27296
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____27302 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars, univ_opening, uu____27302))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____27308  ->
      match uu____27308 with
      | (x,imp) ->
          let uu____27335 = FStar_Syntax_Util.type_u ()  in
          (match uu____27335 with
           | (tu,u) ->
               ((let uu____27357 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____27357
                 then
                   let uu____27360 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____27362 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____27364 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____27360 uu____27362 uu____27364
                 else ());
                (let uu____27369 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu ""
                    in
                 match uu____27369 with
                 | (t,uu____27392,g) ->
                     let uu____27394 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____27410 =
                             tc_tactic FStar_Syntax_Syntax.t_unit
                               FStar_Syntax_Syntax.t_unit env tau
                              in
                           (match uu____27410 with
                            | (tau1,uu____27424,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____27428 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____27394 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3554_27463 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3554_27463.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3554_27463.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____27465 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____27465
                            then
                              let uu____27468 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____27472 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____27468
                                uu____27472
                            else ());
                           (let uu____27477 = push_binding env x1  in
                            (x1, uu____27477, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____27489 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____27489
       then
         let uu____27492 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____27492
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____27605 = tc_binder env1 b  in
             (match uu____27605 with
              | (b1,env',g,u) ->
                  let uu____27654 = aux env' bs2  in
                  (match uu____27654 with
                   | (bs3,env'1,g',us) ->
                       let uu____27715 =
                         let uu____27716 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____27716  in
                       ((b1 :: bs3), env'1, uu____27715, (u :: us))))
          in
       aux env bs)

and (tc_smt_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list * FStar_TypeChecker_Common.guard_t))
  =
  fun en  ->
    fun pats  ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____27824  ->
             fun uu____27825  ->
               match (uu____27824, uu____27825) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____27917 = tc_term en1 t  in
                     match uu____27917 with
                     | (t1,uu____27937,g') ->
                         let uu____27939 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____27939)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____27993  ->
             match uu____27993 with
             | (pats1,g) ->
                 let uu____28020 = tc_args en p  in
                 (match uu____28020 with
                  | (args,g') ->
                      let uu____28033 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____28033))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      Prims.string ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun msg  ->
        let uu____28048 = tc_maybe_toplevel_term env e  in
        match uu____28048 with
        | (e1,c,g) ->
            let uu____28064 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c
               in
            if uu____28064
            then (e1, c, g)
            else
              (let g1 =
                 FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
               let uu____28076 = FStar_TypeChecker_Common.lcomp_comp c  in
               match uu____28076 with
               | (c1,g_c) ->
                   let c2 = norm_c env c1  in
                   let uu____28090 =
                     let uu____28096 =
                       FStar_TypeChecker_Util.is_pure_effect env
                         (FStar_Syntax_Util.comp_effect_name c2)
                        in
                     if uu____28096
                     then
                       let uu____28104 =
                         FStar_Syntax_Syntax.mk_Total
                           (FStar_Syntax_Util.comp_result c2)
                          in
                       (uu____28104, false)
                     else
                       (let uu____28109 =
                          FStar_Syntax_Syntax.mk_GTotal
                            (FStar_Syntax_Util.comp_result c2)
                           in
                        (uu____28109, true))
                      in
                   (match uu____28090 with
                    | (target_comp,allow_ghost) ->
                        let uu____28122 =
                          FStar_TypeChecker_Rel.sub_comp env c2 target_comp
                           in
                        (match uu____28122 with
                         | FStar_Pervasives_Native.Some g' ->
                             let uu____28132 =
                               FStar_TypeChecker_Common.lcomp_of_comp
                                 target_comp
                                in
                             let uu____28133 =
                               let uu____28134 =
                                 FStar_TypeChecker_Env.conj_guard g_c g'  in
                               FStar_TypeChecker_Env.conj_guard g1
                                 uu____28134
                                in
                             (e1, uu____28132, uu____28133)
                         | uu____28135 ->
                             if allow_ghost
                             then
                               let uu____28145 =
                                 FStar_TypeChecker_Err.expected_ghost_expression
                                   e1 c2 msg
                                  in
                               FStar_Errors.raise_error uu____28145
                                 e1.FStar_Syntax_Syntax.pos
                             else
                               (let uu____28159 =
                                  FStar_TypeChecker_Err.expected_pure_expression
                                    e1 c2 msg
                                   in
                                FStar_Errors.raise_error uu____28159
                                  e1.FStar_Syntax_Syntax.pos))))

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  = fun env  -> fun e  -> tc_tot_or_gtot_term' env e ""

and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        Prims.string ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        fun msg  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
          tc_tot_or_gtot_term' env1 e msg

and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env  ->
    fun t  ->
      let uu____28188 = tc_tot_or_gtot_term env t  in
      match uu____28188 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____28219 = tc_check_tot_or_gtot_term env t k ""  in
        match uu____28219 with
        | (t1,uu____28228,g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____28249 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____28249
       then
         let uu____28254 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____28254
       else ());
      (let env1 =
         let uu___3650_28260 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3650_28260.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3650_28260.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3650_28260.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3650_28260.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3650_28260.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3650_28260.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3650_28260.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3650_28260.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3650_28260.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3650_28260.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3650_28260.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3650_28260.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3650_28260.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3650_28260.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3650_28260.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___3650_28260.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___3650_28260.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3650_28260.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3650_28260.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3650_28260.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3650_28260.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3650_28260.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3650_28260.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3650_28260.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3650_28260.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3650_28260.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3650_28260.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3650_28260.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3650_28260.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3650_28260.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3650_28260.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3650_28260.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3650_28260.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3650_28260.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3650_28260.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3650_28260.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3650_28260.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3650_28260.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3650_28260.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3650_28260.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3650_28260.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3650_28260.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3650_28260.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3650_28260.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let uu____28268 =
         try
           (fun uu___3654_28282  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____28303) ->
             let uu____28306 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____28306
          in
       match uu____28268 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____28324 = FStar_TypeChecker_Common.is_total_lcomp c1  in
           if uu____28324
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____28335 =
                let uu____28341 =
                  let uu____28343 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____28343
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____28341)
                 in
              let uu____28347 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____28335 uu____28347))
  
let level_of_type_fail :
  'uuuuuu28363 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'uuuuuu28363
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____28381 =
          let uu____28387 =
            let uu____28389 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____28389 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____28387)  in
        let uu____28393 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____28381 uu____28393
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____28427 =
            let uu____28428 = FStar_Syntax_Util.unrefine t1  in
            uu____28428.FStar_Syntax_Syntax.n  in
          match uu____28427 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____28432 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____28438 = FStar_Syntax_Util.type_u ()  in
                 match uu____28438 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3686_28446 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3686_28446.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3686_28446.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3686_28446.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3686_28446.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3686_28446.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3686_28446.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3686_28446.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3686_28446.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3686_28446.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3686_28446.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3686_28446.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3686_28446.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3686_28446.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3686_28446.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3686_28446.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3686_28446.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3686_28446.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3686_28446.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3686_28446.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3686_28446.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3686_28446.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3686_28446.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3686_28446.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3686_28446.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3686_28446.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3686_28446.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3686_28446.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3686_28446.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3686_28446.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3686_28446.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3686_28446.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3686_28446.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3686_28446.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3686_28446.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3686_28446.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3686_28446.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3686_28446.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3686_28446.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3686_28446.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3686_28446.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3686_28446.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3686_28446.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3686_28446.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3686_28446.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3686_28446.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____28451 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____28451
                       | uu____28453 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u))
           in
        aux true t
  
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun e  ->
      let uu____28470 =
        let uu____28471 = FStar_Syntax_Subst.compress e  in
        uu____28471.FStar_Syntax_Syntax.n  in
      match uu____28470 with
      | FStar_Syntax_Syntax.Tm_bvar uu____28474 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____28477 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____28493 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____28510) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____28555) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____28562 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____28562 with | ((uu____28571,t),uu____28573) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____28579 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____28579
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28582,(FStar_Util.Inl t,uu____28584),uu____28585) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28632,(FStar_Util.Inr c,uu____28634),uu____28635) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____28683 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____28692;
             FStar_Syntax_Syntax.vars = uu____28693;_},us)
          ->
          let uu____28699 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____28699 with
           | ((us',t),uu____28710) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____28717 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____28717)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____28738 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____28740 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____28749) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____28776 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____28776 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____28796  ->
                      match uu____28796 with
                      | (b,uu____28804) ->
                          let uu____28809 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____28809) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____28814 = universe_of_aux env res  in
                 level_of_type env res uu____28814  in
               let u_c =
                 FStar_All.pipe_right c1
                   (FStar_TypeChecker_Util.universe_of_comp env u_res)
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let rec type_of_head retry hd1 args1 =
            let hd2 = FStar_Syntax_Subst.compress hd1  in
            match hd2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____28925 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____28941 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____28971 ->
                let uu____28972 = universe_of_aux env hd2  in
                (uu____28972, args1)
            | FStar_Syntax_Syntax.Tm_name uu____28983 ->
                let uu____28984 = universe_of_aux env hd2  in
                (uu____28984, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____28995 ->
                let uu____29008 = universe_of_aux env hd2  in
                (uu____29008, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____29019 ->
                let uu____29026 = universe_of_aux env hd2  in
                (uu____29026, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____29037 ->
                let uu____29064 = universe_of_aux env hd2  in
                (uu____29064, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____29075 ->
                let uu____29082 = universe_of_aux env hd2  in
                (uu____29082, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____29093 ->
                let uu____29094 = universe_of_aux env hd2  in
                (uu____29094, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____29105 ->
                let uu____29120 = universe_of_aux env hd2  in
                (uu____29120, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____29131 ->
                let uu____29138 = universe_of_aux env hd2  in
                (uu____29138, args1)
            | FStar_Syntax_Syntax.Tm_type uu____29149 ->
                let uu____29150 = universe_of_aux env hd2  in
                (uu____29150, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____29161,hd3::uu____29163) ->
                let uu____29228 = FStar_Syntax_Subst.open_branch hd3  in
                (match uu____29228 with
                 | (uu____29243,uu____29244,hd4) ->
                     let uu____29262 = FStar_Syntax_Util.head_and_args hd4
                        in
                     (match uu____29262 with
                      | (hd5,args') ->
                          type_of_head retry hd5
                            (FStar_List.append args' args1)))
            | uu____29327 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____29329 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____29329 with
                 | (hd3,args2) -> type_of_head false hd3 args2)
            | uu____29387 ->
                let uu____29388 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____29388 with
                 | (env1,uu____29410) ->
                     let env2 =
                       let uu___3847_29416 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3847_29416.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3847_29416.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3847_29416.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3847_29416.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3847_29416.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3847_29416.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3847_29416.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3847_29416.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3847_29416.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3847_29416.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3847_29416.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3847_29416.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3847_29416.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3847_29416.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3847_29416.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3847_29416.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3847_29416.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3847_29416.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3847_29416.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3847_29416.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3847_29416.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3847_29416.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3847_29416.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3847_29416.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3847_29416.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3847_29416.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3847_29416.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3847_29416.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3847_29416.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3847_29416.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3847_29416.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3847_29416.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3847_29416.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3847_29416.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3847_29416.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3847_29416.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3847_29416.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3847_29416.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3847_29416.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3847_29416.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3847_29416.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3847_29416.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3847_29416.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     ((let uu____29421 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____29421
                       then
                         let uu____29426 =
                           let uu____29428 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____29428  in
                         let uu____29429 =
                           FStar_Syntax_Print.term_to_string hd2  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____29426 uu____29429
                       else ());
                      (let uu____29434 = tc_term env2 hd2  in
                       match uu____29434 with
                       | (uu____29455,{
                                        FStar_TypeChecker_Common.eff_name =
                                          uu____29456;
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          uu____29458;
                                        FStar_TypeChecker_Common.comp_thunk =
                                          uu____29459;_},g)
                           ->
                           ((let uu____29477 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____29477
                               (fun uu____29478  -> ()));
                            (t, args1)))))
             in
          let uu____29489 = type_of_head true hd args  in
          (match uu____29489 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____29528 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____29528 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst res1
                    else
                      (let uu____29556 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____29556)))
      | FStar_Syntax_Syntax.Tm_match (uu____29558,hd::uu____29560) ->
          let uu____29625 = FStar_Syntax_Subst.open_branch hd  in
          (match uu____29625 with
           | (uu____29626,uu____29627,hd1) -> universe_of_aux env hd1)
      | FStar_Syntax_Syntax.Tm_match (uu____29645,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____29692 = universe_of_aux env e  in
      level_of_type env e uu____29692
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env0  ->
    fun tps  ->
      let uu____29716 = tc_binders env0 tps  in
      match uu____29716 with
      | (tps1,env,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env0 g; (tps1, env, us))
  
let rec (type_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let mk_tm_type u =
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____29774 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____29792 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____29798 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____29798
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____29800 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29800
            (fun uu____29814  ->
               match uu____29814 with
               | (t2,uu____29822) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____29824;
             FStar_Syntax_Syntax.vars = uu____29825;_},us)
          ->
          let uu____29831 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29831
            (fun uu____29845  ->
               match uu____29845 with
               | (t2,uu____29853) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____29854) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____29856 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____29856
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____29858 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____29858
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____29863;_})
          ->
          let mk_comp =
            let uu____29907 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____29907
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____29938 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____29938
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____30008 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____30008
                 (fun u  ->
                    let uu____30016 =
                      let uu____30019 =
                        let uu____30026 =
                          let uu____30027 =
                            let uu____30042 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____30042)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____30027  in
                        FStar_Syntax_Syntax.mk uu____30026  in
                      uu____30019 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____30016))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____30079 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____30079 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____30138 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____30138
                       (fun uc  ->
                          let uu____30146 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____30146)
                 | (x,imp)::bs3 ->
                     let uu____30172 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____30172
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____30181 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____30201) ->
          let uu____30206 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____30206
            (fun u_x  ->
               let uu____30214 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____30214)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____30219;
             FStar_Syntax_Syntax.vars = uu____30220;_},a::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____30299 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____30299 with
           | (unary_op,uu____30319) ->
               let head =
                 let uu____30347 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                   FStar_Pervasives_Native.None uu____30347
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____30395;
             FStar_Syntax_Syntax.vars = uu____30396;_},a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____30492 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____30492 with
           | (unary_op,uu____30512) ->
               let head =
                 let uu____30540 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   FStar_Pervasives_Native.None uu____30540
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____30596;
             FStar_Syntax_Syntax.vars = uu____30597;_},uu____30598::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____30637;
             FStar_Syntax_Syntax.vars = uu____30638;_},(t2,uu____30640)::uu____30641::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let t_hd = type_of_well_typed_term env hd  in
          let rec aux t_hd1 =
            let uu____30737 =
              let uu____30738 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____30738.FStar_Syntax_Syntax.n  in
            match uu____30737 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____30811 = FStar_Util.first_N n_args bs  in
                    match uu____30811 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____30899 =
                          let uu____30904 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____30904  in
                        (match uu____30899 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____30958 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____30958 with
                       | (bs1,c1) ->
                           let uu____30979 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____30979
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____31061  ->
                     match uu____31061 with
                     | (bs1,t2) ->
                         let subst =
                           FStar_List.map2
                             (fun b  ->
                                fun a  ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args
                            in
                         let uu____31137 = FStar_Syntax_Subst.subst subst t2
                            in
                         FStar_Pervasives_Native.Some uu____31137)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____31139) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____31145,uu____31146) ->
                aux t2
            | uu____31187 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____31188,(FStar_Util.Inl t2,uu____31190),uu____31191) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____31238,(FStar_Util.Inr c,uu____31240),uu____31241) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____31306 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____31306
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____31314) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____31319 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____31342 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____31356 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____31367 = type_of_well_typed_term env t  in
      match uu____31367 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____31373;
            FStar_Syntax_Syntax.vars = uu____31374;_}
          -> FStar_Pervasives_Native.Some u
      | uu____31377 -> FStar_Pervasives_Native.None

let (check_type_of_well_typed_term' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___4126_31405 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4126_31405.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4126_31405.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4126_31405.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4126_31405.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4126_31405.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4126_31405.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4126_31405.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4126_31405.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4126_31405.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4126_31405.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4126_31405.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4126_31405.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4126_31405.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4126_31405.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4126_31405.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4126_31405.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4126_31405.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4126_31405.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4126_31405.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4126_31405.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4126_31405.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4126_31405.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4126_31405.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4126_31405.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4126_31405.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4126_31405.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4126_31405.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4126_31405.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4126_31405.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4126_31405.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4126_31405.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4126_31405.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4126_31405.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4126_31405.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4126_31405.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4126_31405.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4126_31405.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4126_31405.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4126_31405.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4126_31405.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4126_31405.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4126_31405.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4126_31405.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4126_31405.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4126_31405.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____31412 =
            if must_total
            then
              let uu____31414 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____31414 with | (uu____31421,uu____31422,g) -> g
            else
              (let uu____31426 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____31426 with | (uu____31433,uu____31434,g) -> g)
             in
          let uu____31436 = type_of_well_typed_term env2 t  in
          match uu____31436 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____31441 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____31441
                then
                  let uu____31446 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____31448 = FStar_Syntax_Print.term_to_string t  in
                  let uu____31450 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____31452 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____31446 uu____31448 uu____31450 uu____31452
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____31461 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____31461
                 then
                   let uu____31466 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____31468 = FStar_Syntax_Print.term_to_string t  in
                   let uu____31470 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____31472 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____31466
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____31468 uu____31470 uu____31472
                 else ());
                (match g with
                 | FStar_Pervasives_Native.None  -> slow_check ()
                 | FStar_Pervasives_Native.Some g1 -> g1)))
  
let (check_type_of_well_typed_term :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___4157_31509 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4157_31509.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4157_31509.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4157_31509.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4157_31509.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4157_31509.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4157_31509.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4157_31509.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4157_31509.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4157_31509.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4157_31509.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4157_31509.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4157_31509.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4157_31509.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4157_31509.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4157_31509.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4157_31509.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4157_31509.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4157_31509.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4157_31509.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4157_31509.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4157_31509.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4157_31509.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4157_31509.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4157_31509.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4157_31509.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4157_31509.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4157_31509.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4157_31509.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4157_31509.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4157_31509.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4157_31509.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4157_31509.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4157_31509.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4157_31509.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4157_31509.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4157_31509.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4157_31509.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4157_31509.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4157_31509.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4157_31509.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4157_31509.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4157_31509.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4157_31509.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4157_31509.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4157_31509.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____31516 =
            if must_total
            then
              let uu____31518 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____31518 with | (uu____31525,uu____31526,g) -> g
            else
              (let uu____31530 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____31530 with | (uu____31537,uu____31538,g) -> g)
             in
          let uu____31540 =
            let uu____31542 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____31542  in
          if uu____31540
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  