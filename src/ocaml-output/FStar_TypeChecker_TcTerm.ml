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
        (uu___8_5.FStar_TypeChecker_Env.erasable_types_tab);
      FStar_TypeChecker_Env.enable_defer_to_tac =
        (uu___8_5.FStar_TypeChecker_Env.enable_defer_to_tac)
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
        (uu___11_13.FStar_TypeChecker_Env.erasable_types_tab);
      FStar_TypeChecker_Env.enable_defer_to_tac =
        (uu___11_13.FStar_TypeChecker_Env.enable_defer_to_tac)
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
             let uu____50 = FStar_Syntax_Syntax.as_arg v  in
             let uu____59 =
               let uu____70 = FStar_Syntax_Syntax.as_arg tl  in [uu____70]
                in
             uu____50 :: uu____59  in
           FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____49
             r) vs FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___0_111  ->
    match uu___0_111 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____116 -> false
  
let steps : 'uuuuuu125 . 'uuuuuu125 -> FStar_TypeChecker_Env.step Prims.list
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
            | uu____213 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____227 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____227 with
                 | FStar_Pervasives_Native.None  ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____254 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____258 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____258
                            | FStar_Pervasives_Native.Some head ->
                                let uu____262 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____264 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____262 uu____264
                             in
                          let uu____267 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____267
                           in
                        let uu____273 =
                          let uu____286 = FStar_TypeChecker_Env.get_range env
                             in
                          let uu____287 =
                            let uu____288 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____288
                             in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____286 env uu____287
                           in
                        match uu____273 with
                        | (s,uu____303,g0) ->
                            let uu____317 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s  in
                            (match uu____317 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____327 =
                                     FStar_TypeChecker_Env.conj_guard g g0
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____327
                                    in
                                 (s, g1)
                             | uu____328 -> fail ())))
             in
          aux false kt
  
let push_binding :
  'uuuuuu339 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu339) -> FStar_TypeChecker_Env.env
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
        let uu____394 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____394
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
        (let uu___66_424 = lc  in
         {
           FStar_TypeChecker_Common.eff_name =
             (uu___66_424.FStar_TypeChecker_Common.eff_name);
           FStar_TypeChecker_Common.res_typ = t;
           FStar_TypeChecker_Common.cflags =
             (uu___66_424.FStar_TypeChecker_Common.cflags);
           FStar_TypeChecker_Common.comp_thunk =
             (uu___66_424.FStar_TypeChecker_Common.comp_thunk)
         })
  
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> e 
let (maybe_warn_on_use :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv -> unit) =
  fun env  ->
    fun fv  ->
      let uu____447 =
        FStar_TypeChecker_Env.lookup_attrs_of_lid env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      match uu____447 with
      | FStar_Pervasives_Native.None  -> ()
      | FStar_Pervasives_Native.Some attrs ->
          FStar_All.pipe_right attrs
            (FStar_List.iter
               (fun a  ->
                  let uu____470 = FStar_Syntax_Util.head_and_args a  in
                  match uu____470 with
                  | (head,args) ->
                      let msg_arg m =
                        match args with
                        | ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_string (s,uu____524));
                             FStar_Syntax_Syntax.pos = uu____525;
                             FStar_Syntax_Syntax.vars = uu____526;_},uu____527)::[]
                            -> Prims.op_Hat m (Prims.op_Hat ": " s)
                        | uu____555 -> m  in
                      (match head.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar attr_fv when
                           FStar_Ident.lid_equals
                             (attr_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.warn_on_use_attr
                           ->
                           let m =
                             let uu____569 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Util.format1
                               "Every use of %s triggers a warning" uu____569
                              in
                           let uu____572 =
                             FStar_Ident.range_of_lid
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              in
                           FStar_Errors.log_issue uu____572
                             (FStar_Errors.Warning_WarnOnUse, (msg_arg m))
                       | FStar_Syntax_Syntax.Tm_fvar attr_fv when
                           FStar_Ident.lid_equals
                             (attr_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let m =
                             let uu____577 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Util.format1 "%s is deprecated" uu____577
                              in
                           let uu____580 =
                             FStar_Ident.range_of_lid
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              in
                           FStar_Errors.log_issue uu____580
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               (msg_arg m))
                       | uu____582 -> ())))
  
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
                 let uu____628 = FStar_Syntax_Syntax.mk_Total t  in
                 FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                   uu____628
             | FStar_Util.Inr lc -> lc  in
           let t = lc.FStar_TypeChecker_Common.res_typ  in
           let uu____631 =
             let uu____638 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____638 with
             | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____648 =
                   FStar_TypeChecker_Util.check_has_type env e lc t'  in
                 (match uu____648 with
                  | (e1,lc1,g) ->
                      ((let uu____665 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Medium
                           in
                        if uu____665
                        then
                          let uu____668 =
                            FStar_TypeChecker_Common.lcomp_to_string lc1  in
                          let uu____670 =
                            FStar_Syntax_Print.term_to_string t'  in
                          let uu____672 =
                            FStar_TypeChecker_Rel.guard_to_string env g  in
                          let uu____674 =
                            FStar_TypeChecker_Rel.guard_to_string env guard
                             in
                          FStar_Util.print4
                            "value_check_expected_typ: type is %s<:%s \tguard is %s, %s\n"
                            uu____668 uu____670 uu____672 uu____674
                        else ());
                       (let t1 = lc1.FStar_TypeChecker_Common.res_typ  in
                        let g1 = FStar_TypeChecker_Env.conj_guard g guard  in
                        let msg =
                          let uu____688 =
                            FStar_TypeChecker_Env.is_trivial_guard_formula g1
                             in
                          if uu____688
                          then FStar_Pervasives_Native.None
                          else
                            FStar_All.pipe_left
                              (fun uu____717  ->
                                 FStar_Pervasives_Native.Some uu____717)
                              (FStar_TypeChecker_Err.subtyping_failed env t1
                                 t')
                           in
                        let uu____718 =
                          FStar_TypeChecker_Util.strengthen_precondition msg
                            env e1 lc1 g1
                           in
                        match uu____718 with
                        | (lc2,g2) ->
                            let uu____731 = set_lcomp_result lc2 t'  in
                            ((memo_tk e1 t'), uu____731, g2))))
              in
           match uu____631 with | (e1,lc1,g) -> (e1, lc1, g))
  
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
        let uu____769 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____769 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____779 = FStar_TypeChecker_Util.maybe_coerce_lc env e lc t
               in
            (match uu____779 with
             | (e1,lc1,g_c) ->
                 let uu____795 =
                   FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t  in
                 (match uu____795 with
                  | (e2,lc2,g) ->
                      let uu____811 = FStar_TypeChecker_Env.conj_guard g g_c
                         in
                      (e2, lc2, uu____811)))
  
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
        let uu____852 = ec  in
        match uu____852 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____875 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____875
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____880 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____880
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____886 =
              let ct = FStar_Syntax_Util.comp_result c  in
              match copt with
              | FStar_Pervasives_Native.Some uu____910 ->
                  (copt, c, FStar_Pervasives_Native.None)
              | FStar_Pervasives_Native.None  ->
                  let uu____915 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____918 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____918))
                     in
                  if uu____915
                  then
                    let uu____931 =
                      let uu____934 =
                        FStar_Syntax_Util.ml_comp ct
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____934  in
                    (uu____931, c, FStar_Pervasives_Native.None)
                  else
                    (let uu____941 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____941
                     then
                       let uu____954 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____954,
                         FStar_Pervasives_Native.None)
                     else
                       (let uu____961 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____961
                        then
                          let uu____974 =
                            let uu____977 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____977  in
                          (uu____974, c, FStar_Pervasives_Native.None)
                        else
                          (let uu____984 =
                             let uu____986 =
                               FStar_All.pipe_right
                                 (FStar_Syntax_Util.comp_effect_name c)
                                 (FStar_TypeChecker_Env.norm_eff_name env)
                                in
                             FStar_All.pipe_right uu____986
                               (FStar_TypeChecker_Env.is_layered_effect env)
                              in
                           if uu____984
                           then
                             let uu____999 =
                               let uu____1005 =
                                 let uu____1007 =
                                   let uu____1009 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name
                                      in
                                   FStar_All.pipe_right uu____1009
                                     FStar_Ident.string_of_lid
                                    in
                                 let uu____1013 =
                                   FStar_Range.string_of_range
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_Util.format2
                                   "Missing annotation for a layered effect (%s) computation at %s"
                                   uu____1007 uu____1013
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____1005)  in
                             FStar_Errors.raise_error uu____999
                               e.FStar_Syntax_Syntax.pos
                           else
                             (let uu____1029 =
                                FStar_Options.trivial_pre_for_unannotated_effectful_fns
                                  ()
                                 in
                              if uu____1029
                              then
                                let uu____1042 =
                                  let uu____1045 =
                                    FStar_TypeChecker_Util.check_trivial_precondition
                                      env c
                                     in
                                  match uu____1045 with
                                  | (uu____1054,uu____1055,g) ->
                                      FStar_Pervasives_Native.Some g
                                   in
                                (FStar_Pervasives_Native.None, c, uu____1042)
                              else
                                (FStar_Pervasives_Native.None, c,
                                  FStar_Pervasives_Native.None)))))
               in
            (match uu____886 with
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
                        | FStar_Pervasives_Native.Some uu____1094 ->
                            failwith
                              "Impossible! check_expected_effect, gopt should have been None");
                       (let c3 =
                          let uu____1097 =
                            FStar_TypeChecker_Common.lcomp_of_comp c2  in
                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                            env e uu____1097
                           in
                        let uu____1098 =
                          FStar_TypeChecker_Common.lcomp_comp c3  in
                        match uu____1098 with
                        | (c4,g_c) ->
                            ((let uu____1112 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Medium
                                 in
                              if uu____1112
                              then
                                let uu____1116 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____1118 =
                                  FStar_Syntax_Print.comp_to_string c4  in
                                let uu____1120 =
                                  FStar_Syntax_Print.comp_to_string
                                    expected_c
                                   in
                                FStar_Util.print3
                                  "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                                  uu____1116 uu____1118 uu____1120
                              else ());
                             (let uu____1125 =
                                FStar_TypeChecker_Util.check_comp env e c4
                                  expected_c
                                 in
                              match uu____1125 with
                              | (e1,uu____1139,g) ->
                                  let g1 =
                                    let uu____1142 =
                                      FStar_TypeChecker_Env.get_range env  in
                                    FStar_TypeChecker_Util.label_guard
                                      uu____1142
                                      "could not prove post-condition" g
                                     in
                                  ((let uu____1145 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Medium
                                       in
                                    if uu____1145
                                    then
                                      let uu____1148 =
                                        FStar_Range.string_of_range
                                          e1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____1150 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          env g1
                                         in
                                      FStar_Util.print2
                                        "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                        uu____1148 uu____1150
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
                                    let uu____1156 =
                                      FStar_TypeChecker_Env.conj_guard g_c g1
                                       in
                                    (e2, expected_c, uu____1156)))))))))
  
let no_logical_guard :
  'uuuuuu1166 'uuuuuu1167 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1166 * 'uuuuuu1167 * FStar_TypeChecker_Env.guard_t) ->
        ('uuuuuu1166 * 'uuuuuu1167 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____1189  ->
      match uu____1189 with
      | (te,kt,f) ->
          let uu____1199 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____1199 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____1207 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____1213 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____1207 uu____1213)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____1226 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____1226 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____1231 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____1231
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1261 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1261 with
        | (head,args) ->
            let uu____1306 =
              let uu____1321 =
                let uu____1322 = FStar_Syntax_Util.un_uinst head  in
                uu____1322.FStar_Syntax_Syntax.n  in
              (uu____1321, args)  in
            (match uu____1306 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1338) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1365,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1366))::(hd,FStar_Pervasives_Native.None
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
                fv,(uu____1443,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1444))::(pat,FStar_Pervasives_Native.None
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
             | uu____1528 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
  
let (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats 
let check_pat_fvs :
  'uuuuuu1572 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'uuuuuu1572) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1608 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1615 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1608 uu____1615  in
          let uu____1616 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1643  ->
                    match uu____1643 with
                    | (b,uu____1650) ->
                        let uu____1651 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1651))
             in
          match uu____1616 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1658) ->
              let uu____1663 =
                let uu____1669 =
                  let uu____1671 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1671
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1669)  in
              FStar_Errors.log_issue rng uu____1663
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1697 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1697 with
        | (head,args) ->
            let uu____1742 =
              let uu____1757 =
                let uu____1758 = FStar_Syntax_Util.un_uinst head  in
                uu____1758.FStar_Syntax_Syntax.n  in
              (uu____1757, args)  in
            (match uu____1742 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1774) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1796::(hd,uu____1798)::(tl,uu____1800)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1867 = pat_terms hd  in
                 let uu____1870 = pat_terms tl  in
                 FStar_List.append uu____1867 uu____1870
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1874::(pat,uu____1876)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1961 -> [])
         in
      let rec aux t1 =
        let uu____1986 =
          let uu____1987 = FStar_Syntax_Subst.compress t1  in
          uu____1987.FStar_Syntax_Syntax.n  in
        match uu____1986 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1992 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1993 -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1994 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1995 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1996 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____2009 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_abs uu____2010 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____2029 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____2044 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____2051 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____2074 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____2088 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____2103 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____2111 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____2111 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____2144 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____2161  ->
                   match uu____2161 with
                   | (t3,uu____2173) ->
                       let uu____2178 = aux t3  in
                       FStar_List.append acc uu____2178) uu____2144 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2182,uu____2183) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2225) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2231) -> aux t2  in
      let tlist =
        let uu____2239 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____2239 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = Prims.int_zero
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____2262 =
                    let uu____2264 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____2264  in
                  Prims.op_Hat s uu____2262) "" tlist
            in
         let uu____2268 =
           let uu____2274 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2274)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2268)
  
let check_smt_pat :
  'uuuuuu2289 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu2289) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2330 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2330
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2333;
                  FStar_Syntax_Syntax.effect_name = uu____2334;
                  FStar_Syntax_Syntax.result_typ = uu____2335;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2339)::[];
                  FStar_Syntax_Syntax.flags = uu____2340;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2402 -> failwith "Impossible"
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
              let uu___396_2471 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___396_2471.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___396_2471.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___396_2471.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___396_2471.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___396_2471.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___396_2471.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___396_2471.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___396_2471.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___396_2471.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___396_2471.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___396_2471.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___396_2471.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___396_2471.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___396_2471.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___396_2471.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___396_2471.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.use_eq_strict =
                  (uu___396_2471.FStar_TypeChecker_Env.use_eq_strict);
                FStar_TypeChecker_Env.is_iface =
                  (uu___396_2471.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___396_2471.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___396_2471.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___396_2471.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___396_2471.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___396_2471.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___396_2471.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___396_2471.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___396_2471.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___396_2471.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___396_2471.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___396_2471.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___396_2471.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___396_2471.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___396_2471.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___396_2471.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___396_2471.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___396_2471.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.try_solve_implicits_hook =
                  (uu___396_2471.FStar_TypeChecker_Env.try_solve_implicits_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___396_2471.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.mpreprocess =
                  (uu___396_2471.FStar_TypeChecker_Env.mpreprocess);
                FStar_TypeChecker_Env.postprocess =
                  (uu___396_2471.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___396_2471.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___396_2471.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___396_2471.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___396_2471.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (uu___396_2471.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (uu___396_2471.FStar_TypeChecker_Env.erasable_types_tab);
                FStar_TypeChecker_Env.enable_defer_to_tac =
                  (uu___396_2471.FStar_TypeChecker_Env.enable_defer_to_tac)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2500 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2500
               then
                 let uu____2503 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2506 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2503 uu____2506
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2540  ->
                         match uu____2540 with
                         | (b,uu____2550) ->
                             let t =
                               let uu____2556 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2556
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2559 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2560 -> []
                              | uu____2575 ->
                                  let uu____2576 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2576])))
                  in
               let as_lex_list dec =
                 let uu____2589 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2589 with
                 | (head,uu____2609) ->
                     (match head.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2637 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2645 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2654  ->
                         match uu___1_2654 with
                         | FStar_Syntax_Syntax.DECREASES uu____2656 -> true
                         | uu____2660 -> false))
                  in
               match uu____2645 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2667 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   mk_lex_list xs)
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2704 =
              match uu____2704 with
              | (l,arity,t,u_names) ->
                  let uu____2728 =
                    FStar_TypeChecker_Normalize.get_n_binders env1 arity t
                     in
                  (match uu____2728 with
                   | (formals,c) ->
                       (if arity > (FStar_List.length formals)
                        then
                          failwith
                            "impossible: bad formals arity, guard_one_letrec"
                        else ();
                        (let formals1 =
                           FStar_All.pipe_right formals
                             (FStar_List.map
                                (fun uu____2796  ->
                                   match uu____2796 with
                                   | (x,imp) ->
                                       let uu____2815 =
                                         FStar_Syntax_Syntax.is_null_bv x  in
                                       if uu____2815
                                       then
                                         let uu____2824 =
                                           let uu____2825 =
                                             let uu____2828 =
                                               FStar_Syntax_Syntax.range_of_bv
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____2828
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____2825
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         (uu____2824, imp)
                                       else (x, imp)))
                            in
                         let dec = decreases_clause formals1 c  in
                         let precedes1 =
                           let uu____2839 =
                             let uu____2840 = FStar_Syntax_Syntax.as_arg dec
                                in
                             let uu____2849 =
                               let uu____2860 =
                                 FStar_Syntax_Syntax.as_arg previous_dec  in
                               [uu____2860]  in
                             uu____2840 :: uu____2849  in
                           FStar_Syntax_Syntax.mk_Tm_app precedes uu____2839
                             r
                            in
                         let precedes2 =
                           FStar_TypeChecker_Util.label
                             "Could not prove termination of this recursive call"
                             r precedes1
                            in
                         let uu____2895 = FStar_Util.prefix formals1  in
                         match uu____2895 with
                         | (bs,(last,imp)) ->
                             let last1 =
                               let uu___459_2958 = last  in
                               let uu____2959 =
                                 FStar_Syntax_Util.refine last precedes2  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___459_2958.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___459_2958.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____2959
                               }  in
                             let refined_formals =
                               FStar_List.append bs [(last1, imp)]  in
                             let t' =
                               FStar_Syntax_Util.arrow refined_formals c  in
                             ((let uu____2995 =
                                 FStar_TypeChecker_Env.debug env1
                                   FStar_Options.Medium
                                  in
                               if uu____2995
                               then
                                 let uu____2998 =
                                   FStar_Syntax_Print.lbname_to_string l  in
                                 let uu____3000 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 let uu____3002 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print3
                                   "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                   uu____2998 uu____3000 uu____3002
                               else ());
                              (l, t', u_names)))))
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
               let uu____3064 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____3064)
  
let (is_comp_ascribed_reflect :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____3087 =
      let uu____3088 = FStar_Syntax_Subst.compress e  in
      uu____3088.FStar_Syntax_Syntax.n  in
    match uu____3087 with
    | FStar_Syntax_Syntax.Tm_ascribed
        (e1,(FStar_Util.Inr uu____3100,uu____3101),uu____3102) ->
        let uu____3149 =
          let uu____3150 = FStar_Syntax_Subst.compress e1  in
          uu____3150.FStar_Syntax_Syntax.n  in
        (match uu____3149 with
         | FStar_Syntax_Syntax.Tm_app (head,args) when
             (FStar_List.length args) = Prims.int_one ->
             let uu____3197 =
               let uu____3198 = FStar_Syntax_Subst.compress head  in
               uu____3198.FStar_Syntax_Syntax.n  in
             (match uu____3197 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect l)
                  ->
                  let uu____3210 =
                    let uu____3217 = FStar_All.pipe_right args FStar_List.hd
                       in
                    FStar_All.pipe_right uu____3217
                      (fun uu____3273  ->
                         match uu____3273 with | (e2,aqual) -> (l, e2, aqual))
                     in
                  FStar_All.pipe_right uu____3210
                    (fun uu____3326  ->
                       FStar_Pervasives_Native.Some uu____3326)
              | uu____3327 -> FStar_Pervasives_Native.None)
         | uu____3334 -> FStar_Pervasives_Native.None)
    | uu____3341 -> FStar_Pervasives_Native.None
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____4066 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____4066
       then
         let uu____4069 =
           let uu____4071 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____4071  in
         let uu____4073 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1  in
         let uu____4075 = FStar_Syntax_Print.term_to_string e  in
         let uu____4077 =
           let uu____4079 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____4079  in
         let uu____4080 =
           let uu____4082 = FStar_TypeChecker_Env.expected_typ env  in
           match uu____4082 with
           | FStar_Pervasives_Native.None  -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t
            in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____4069 uu____4073 uu____4075 uu____4077 uu____4080
       else ());
      (let uu____4091 =
         FStar_Util.record_time
           (fun uu____4110  ->
              tc_maybe_toplevel_term
                (let uu___502_4113 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___502_4113.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___502_4113.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___502_4113.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___502_4113.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___502_4113.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___502_4113.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___502_4113.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___502_4113.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___502_4113.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___502_4113.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___502_4113.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___502_4113.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___502_4113.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___502_4113.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___502_4113.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___502_4113.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___502_4113.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___502_4113.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___502_4113.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___502_4113.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___502_4113.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___502_4113.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___502_4113.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___502_4113.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___502_4113.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___502_4113.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___502_4113.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___502_4113.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___502_4113.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___502_4113.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___502_4113.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___502_4113.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___502_4113.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___502_4113.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___502_4113.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___502_4113.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___502_4113.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___502_4113.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___502_4113.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___502_4113.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___502_4113.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___502_4113.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___502_4113.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___502_4113.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___502_4113.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___502_4113.FStar_TypeChecker_Env.enable_defer_to_tac)
                 }) e)
          in
       match uu____4091 with
       | (r,ms) ->
           ((let uu____4138 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____4138
             then
               ((let uu____4142 =
                   let uu____4144 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____4144
                    in
                 let uu____4146 = FStar_Syntax_Print.term_to_string e  in
                 let uu____4148 =
                   let uu____4150 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____4150  in
                 let uu____4151 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____4142 uu____4146 uu____4148 uu____4151);
                (let uu____4154 = r  in
                 match uu____4154 with
                 | (e1,lc,uu____4163) ->
                     let uu____4164 =
                       let uu____4166 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____4166
                        in
                     let uu____4168 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____4170 =
                       FStar_TypeChecker_Common.lcomp_to_string lc  in
                     let uu____4172 =
                       let uu____4174 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____4174  in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____4164 uu____4168 uu____4170 uu____4172))
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
      (let uu____4192 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____4192
       then
         let uu____4195 =
           let uu____4197 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____4197  in
         let uu____4199 = FStar_Syntax_Print.tag_of_term top  in
         let uu____4201 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____4195 uu____4199
           uu____4201
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4212 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____4234 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____4241 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____4254 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____4255 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____4256 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____4257 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____4258 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4277 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4292 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4299 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_4315 =
             match uu___2_4315 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4321 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name t =
               let uu____4337 =
                 let uu____4338 = FStar_Syntax_Subst.compress t  in
                 uu____4338.FStar_Syntax_Syntax.n  in
               match uu____4337 with
               | FStar_Syntax_Syntax.Tm_name uu____4342 -> true
               | uu____4344 -> false  in
             FStar_Util.for_some
               (fun uu____4354  ->
                  match uu____4354 with
                  | (uu____4360,t) ->
                      let uu____4362 = is_name t  in
                      Prims.op_Negation uu____4362)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____4381  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____4424  ->
                       match uu____4424 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___575_4453 = qi  in
                  let uu____4454 =
                    FStar_List.map
                      (fun uu____4482  ->
                         match uu____4482 with
                         | ((bv,uu____4498),bv') ->
                             let uu____4510 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____4510)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___575_4453.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4454
                  }  in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    top.FStar_Syntax_Syntax.pos
                   in
                let e1 =
                  FStar_List.fold_left
                    (fun t  ->
                       fun lb  ->
                         let uu____4522 =
                           let uu____4523 =
                             let uu____4537 =
                               let uu____4540 =
                                 let uu____4541 =
                                   let uu____4548 =
                                     projl lb.FStar_Syntax_Syntax.lbname  in
                                   FStar_Syntax_Syntax.mk_binder uu____4548
                                    in
                                 [uu____4541]  in
                               FStar_Syntax_Subst.close uu____4540 t  in
                             ((false, [lb]), uu____4537)  in
                           FStar_Syntax_Syntax.Tm_let uu____4523  in
                         FStar_Syntax_Syntax.mk uu____4522
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4584 =
                  FStar_List.fold_right
                    (fun uu____4620  ->
                       fun uu____4621  ->
                         match (uu____4620, uu____4621) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4690 = tc_term env_tm tm  in
                             (match uu____4690 with
                              | (tm1,uu____4708,g) ->
                                  let uu____4710 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4710))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4584 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___603_4752 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___603_4752.FStar_Syntax_Syntax.qkind);
                         FStar_Syntax_Syntax.antiquotes =
                           (FStar_List.rev aqs_rev)
                       }  in
                     let tm =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                         top.FStar_Syntax_Syntax.pos
                        in
                     value_check_expected_typ env1 tm
                       (FStar_Util.Inl FStar_Syntax_Syntax.t_term) guard)
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let c = FStar_Syntax_Syntax.mk_Tac FStar_Syntax_Syntax.t_term
                   in
                let uu____4763 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4763 with
                 | (env',uu____4777) ->
                     let uu____4782 =
                       tc_term
                         (let uu___612_4791 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___612_4791.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___612_4791.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___612_4791.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___612_4791.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___612_4791.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___612_4791.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___612_4791.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___612_4791.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___612_4791.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___612_4791.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___612_4791.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___612_4791.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___612_4791.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___612_4791.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___612_4791.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___612_4791.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___612_4791.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___612_4791.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___612_4791.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___612_4791.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___612_4791.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___612_4791.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___612_4791.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___612_4791.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___612_4791.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___612_4791.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___612_4791.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___612_4791.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___612_4791.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___612_4791.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___612_4791.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___612_4791.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___612_4791.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___612_4791.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___612_4791.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___612_4791.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___612_4791.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___612_4791.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___612_4791.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___612_4791.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___612_4791.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___612_4791.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___612_4791.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___612_4791.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___612_4791.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___612_4791.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) qt
                        in
                     (match uu____4782 with
                      | (qt1,uu____4800,uu____4801) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4807 =
                            let uu____4814 =
                              let uu____4819 =
                                FStar_TypeChecker_Common.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4819  in
                            value_check_expected_typ env1 top uu____4814
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4807 with
                           | (t1,lc,g) ->
                               let t2 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (t1,
                                        (FStar_Syntax_Syntax.Meta_monadic_lift
                                           (FStar_Parser_Const.effect_PURE_lid,
                                             FStar_Parser_Const.effect_TAC_lid,
                                             FStar_Syntax_Syntax.t_term))))
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               (t2, lc, g)))))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____4836;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4837;
             FStar_Syntax_Syntax.ltyp = uu____4838;
             FStar_Syntax_Syntax.rng = uu____4839;_}
           ->
           let uu____4850 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4850
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4857 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4857 with
            | (e2,c,g) ->
                let g1 =
                  let uu___642_4874 = g  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___642_4874.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___642_4874.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___642_4874.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___642_4874.FStar_TypeChecker_Common.implicits)
                  }  in
                let uu____4875 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    top.FStar_Syntax_Syntax.pos
                   in
                (uu____4875, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names,pats)) ->
           let uu____4917 = FStar_Syntax_Util.type_u ()  in
           (match uu____4917 with
            | (t,u) ->
                let uu____4930 = tc_check_tot_or_gtot_term env1 e1 t ""  in
                (match uu____4930 with
                 | (e2,c,g) ->
                     let uu____4947 =
                       let uu____4964 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4964 with
                       | (env2,uu____4988) -> tc_smt_pats env2 pats  in
                     (match uu____4947 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___665_5026 = g'  in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred_to_tac =
                                (uu___665_5026.FStar_TypeChecker_Common.deferred_to_tac);
                              FStar_TypeChecker_Common.deferred =
                                (uu___665_5026.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___665_5026.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___665_5026.FStar_TypeChecker_Common.implicits)
                            }  in
                          let uu____5027 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names, pats1))))
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____5046 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____5027, c, uu____5046))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____5052 =
             let uu____5053 = FStar_Syntax_Subst.compress e1  in
             uu____5053.FStar_Syntax_Syntax.n  in
           (match uu____5052 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____5062,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____5064;
                               FStar_Syntax_Syntax.lbtyp = uu____5065;
                               FStar_Syntax_Syntax.lbeff = uu____5066;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____5068;
                               FStar_Syntax_Syntax.lbpos = uu____5069;_}::[]),e2)
                ->
                let uu____5100 =
                  let uu____5107 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____5107 e11  in
                (match uu____5100 with
                 | (e12,c1,g1) ->
                     let uu____5117 = tc_term env1 e2  in
                     (match uu____5117 with
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
                            let uu____5141 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name
                               in
                            if uu____5141
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____5151 =
                              let uu____5152 =
                                let uu____5166 =
                                  let uu____5174 =
                                    let uu____5177 =
                                      FStar_Syntax_Syntax.mk_lb
                                        (x, [],
                                          (c1.FStar_TypeChecker_Common.eff_name),
                                          FStar_Syntax_Syntax.t_unit, e13,
                                          attrs,
                                          (e13.FStar_Syntax_Syntax.pos))
                                       in
                                    [uu____5177]  in
                                  (false, uu____5174)  in
                                (uu____5166, e22)  in
                              FStar_Syntax_Syntax.Tm_let uu____5152  in
                            FStar_Syntax_Syntax.mk uu____5151
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
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____5201 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____5201)))
            | uu____5202 ->
                let uu____5203 = tc_term env1 e1  in
                (match uu____5203 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____5225) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____5237) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____5256 = tc_term env1 e1  in
           (match uu____5256 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____5277,(FStar_Util.Inr expected_c,_tacopt),uu____5280) when
           let uu____5327 = FStar_All.pipe_right top is_comp_ascribed_reflect
              in
           FStar_All.pipe_right uu____5327 FStar_Util.is_some ->
           let uu____5359 =
             let uu____5370 =
               FStar_All.pipe_right top is_comp_ascribed_reflect  in
             FStar_All.pipe_right uu____5370 FStar_Util.must  in
           (match uu____5359 with
            | (effect_lid,e1,aqual) ->
                let uu____5444 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____5444 with
                 | (env0,uu____5458) ->
                     let uu____5463 = tc_comp env0 expected_c  in
                     (match uu____5463 with
                      | (expected_c1,uu____5477,g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1
                             in
                          ((let uu____5481 =
                              let uu____5483 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name
                                 in
                              Prims.op_Negation uu____5483  in
                            if uu____5481
                            then
                              let uu____5486 =
                                let uu____5492 =
                                  let uu____5494 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  let uu____5496 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5494 uu____5496
                                   in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5492)
                                 in
                              FStar_Errors.raise_error uu____5486
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5503 =
                              let uu____5505 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid
                                 in
                              Prims.op_Negation uu____5505  in
                            if uu____5503
                            then
                              let uu____5508 =
                                let uu____5514 =
                                  let uu____5516 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5516
                                   in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5514)
                                 in
                              FStar_Errors.raise_error uu____5508
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd
                               in
                            let repr =
                              let uu____5526 =
                                let uu____5529 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp
                                   in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5529 u_c
                                 in
                              FStar_All.pipe_right uu____5526 FStar_Util.must
                               in
                            let e2 =
                              let uu____5535 =
                                let uu____5536 =
                                  let uu____5563 =
                                    let uu____5580 =
                                      let uu____5589 =
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          (FStar_Pervasives_Native.Some u_c)
                                         in
                                      FStar_Util.Inr uu____5589  in
                                    (uu____5580,
                                      FStar_Pervasives_Native.None)
                                     in
                                  (e1, uu____5563,
                                    FStar_Pervasives_Native.None)
                                   in
                                FStar_Syntax_Syntax.Tm_ascribed uu____5536
                                 in
                              FStar_Syntax_Syntax.mk uu____5535
                                e1.FStar_Syntax_Syntax.pos
                               in
                            (let uu____5631 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme
                                in
                             if uu____5631
                             then
                               let uu____5635 =
                                 FStar_Syntax_Print.term_to_string e2  in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5635
                             else ());
                            (let uu____5640 = tc_tot_or_gtot_term env0 e2  in
                             match uu____5640 with
                             | (e3,uu____5654,g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3  in
                                 ((let uu____5658 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme
                                      in
                                   if uu____5658
                                   then
                                     let uu____5662 =
                                       FStar_Syntax_Print.term_to_string e4
                                        in
                                     let uu____5664 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e
                                        in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5662 uu____5664
                                   else ());
                                  (let top1 =
                                     let r = top.FStar_Syntax_Syntax.pos  in
                                     let tm =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_reflect
                                               effect_lid)) r
                                        in
                                     let tm1 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (tm, [(e4, aqual)])) r
                                        in
                                     let uu____5711 =
                                       let uu____5712 =
                                         let uu____5739 =
                                           let uu____5742 =
                                             FStar_All.pipe_right expected_c1
                                               FStar_Syntax_Util.comp_effect_name
                                              in
                                           FStar_All.pipe_right uu____5742
                                             (fun uu____5747  ->
                                                FStar_Pervasives_Native.Some
                                                  uu____5747)
                                            in
                                         (tm1,
                                           ((FStar_Util.Inr expected_c1),
                                             _tacopt), uu____5739)
                                          in
                                       FStar_Syntax_Syntax.Tm_ascribed
                                         uu____5712
                                        in
                                     FStar_Syntax_Syntax.mk uu____5711 r  in
                                   let uu____5784 =
                                     let uu____5791 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     comp_check_expected_typ env1 top1
                                       uu____5791
                                      in
                                   match uu____5784 with
                                   | (top2,c,g_env) ->
                                       let uu____5801 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env]
                                          in
                                       (top2, c, uu____5801)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____5805) ->
           let uu____5852 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____5852 with
            | (env0,uu____5866) ->
                let uu____5871 = tc_comp env0 expected_c  in
                (match uu____5871 with
                 | (expected_c1,uu____5885,g) ->
                     let uu____5887 =
                       let uu____5894 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____5894 e1  in
                     (match uu____5887 with
                      | (e2,c',g') ->
                          let uu____5904 =
                            let uu____5915 =
                              FStar_TypeChecker_Common.lcomp_comp c'  in
                            match uu____5915 with
                            | (c'1,g_c') ->
                                let uu____5932 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1)
                                   in
                                (match uu____5932 with
                                 | (e3,expected_c2,g'') ->
                                     let uu____5952 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g''
                                        in
                                     (e3, expected_c2, uu____5952))
                             in
                          (match uu____5904 with
                           | (e3,expected_c2,g'') ->
                               let uu____5974 = tc_tactic_opt env0 topt  in
                               (match uu____5974 with
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
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let lc =
                                      FStar_TypeChecker_Common.lcomp_of_comp
                                        expected_c2
                                       in
                                    let f =
                                      let uu____6034 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____6034
                                       in
                                    let uu____6035 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____6035 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____6052 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____6052
                                            in
                                         let uu____6053 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____6053)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____6057) ->
           let uu____6104 = FStar_Syntax_Util.type_u ()  in
           (match uu____6104 with
            | (k,u) ->
                let uu____6117 = tc_check_tot_or_gtot_term env1 t k ""  in
                (match uu____6117 with
                 | (t1,uu____6132,f) ->
                     let uu____6134 = tc_tactic_opt env1 topt  in
                     (match uu____6134 with
                      | (topt1,gtac) ->
                          let uu____6153 =
                            let uu____6160 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____6160 e1  in
                          (match uu____6153 with
                           | (e2,c,g) ->
                               let uu____6170 =
                                 let uu____6175 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____6181  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____6175 e2 c f
                                  in
                               (match uu____6170 with
                                | (c1,f1) ->
                                    let uu____6191 =
                                      let uu____6198 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_TypeChecker_Common.eff_name))))
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____6198
                                        c1
                                       in
                                    (match uu____6191 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____6245 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____6245
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____6247 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____6247)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6248;
              FStar_Syntax_Syntax.vars = uu____6249;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6328 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6328 with
            | (unary_op,uu____6352) ->
                let head =
                  let uu____6380 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6380
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6428;
              FStar_Syntax_Syntax.vars = uu____6429;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6508 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6508 with
            | (unary_op,uu____6532) ->
                let head =
                  let uu____6560 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6560
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6608);
              FStar_Syntax_Syntax.pos = uu____6609;
              FStar_Syntax_Syntax.vars = uu____6610;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6689 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6689 with
            | (unary_op,uu____6713) ->
                let head =
                  let uu____6741 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6741
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6789;
              FStar_Syntax_Syntax.vars = uu____6790;_},a1::a2::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6886 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6886 with
            | (unary_op,uu____6910) ->
                let head =
                  let uu____6938 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    uu____6938
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6994;
              FStar_Syntax_Syntax.vars = uu____6995;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____7033 =
             let uu____7040 =
               let uu____7041 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7041  in
             tc_term uu____7040 e1  in
           (match uu____7033 with
            | (e2,c,g) ->
                let uu____7065 = FStar_Syntax_Util.head_and_args top  in
                (match uu____7065 with
                 | (head,uu____7089) ->
                     let uu____7114 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head, [(e2, FStar_Pervasives_Native.None)]))
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____7147 =
                       let uu____7148 =
                         let uu____7149 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____7149  in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7148
                        in
                     (uu____7114, uu____7147, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7150;
              FStar_Syntax_Syntax.vars = uu____7151;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____7204 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7204 with
            | (head,uu____7228) ->
                let env' =
                  let uu____7254 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____7254  in
                let uu____7255 = tc_term env' r  in
                (match uu____7255 with
                 | (er,uu____7269,gr) ->
                     let uu____7271 = tc_term env1 t  in
                     (match uu____7271 with
                      | (t1,tt,gt) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt  in
                          let uu____7288 =
                            let uu____7289 =
                              let uu____7290 = FStar_Syntax_Syntax.as_arg t1
                                 in
                              let uu____7299 =
                                let uu____7310 = FStar_Syntax_Syntax.as_arg r
                                   in
                                [uu____7310]  in
                              uu____7290 :: uu____7299  in
                            FStar_Syntax_Syntax.mk_Tm_app head uu____7289
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____7288, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____7343;
              FStar_Syntax_Syntax.vars = uu____7344;_},uu____7345)
           ->
           let uu____7370 =
             let uu____7376 =
               let uu____7378 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7378  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7376)  in
           FStar_Errors.raise_error uu____7370 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7388;
              FStar_Syntax_Syntax.vars = uu____7389;_},uu____7390)
           ->
           let uu____7415 =
             let uu____7421 =
               let uu____7423 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7423  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7421)  in
           FStar_Errors.raise_error uu____7415 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____7433;
              FStar_Syntax_Syntax.vars = uu____7434;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7481 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____7481 with
             | (env0,uu____7495) ->
                 let uu____7500 = tc_term env0 e1  in
                 (match uu____7500 with
                  | (e2,c,g) ->
                      let uu____7516 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____7516 with
                       | (reify_op,uu____7540) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____7566 =
                             FStar_TypeChecker_Common.lcomp_comp c  in
                           (match uu____7566 with
                            | (c1,g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1  in
                                ((let uu____7581 =
                                    let uu____7583 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef
                                       in
                                    Prims.op_Negation uu____7583  in
                                  if uu____7581
                                  then
                                    let uu____7586 =
                                      let uu____7592 =
                                        let uu____7594 =
                                          FStar_Ident.string_of_lid ef  in
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          uu____7594
                                         in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7592)
                                       in
                                    FStar_Errors.raise_error uu____7586
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
                                      top.FStar_Syntax_Syntax.pos
                                     in
                                  let c2 =
                                    let uu____7637 =
                                      (FStar_TypeChecker_Env.is_total_effect
                                         env1 ef)
                                        ||
                                        (let uu____7640 =
                                           FStar_All.pipe_right ef
                                             (FStar_TypeChecker_Env.norm_eff_name
                                                env1)
                                            in
                                         FStar_All.pipe_right uu____7640
                                           (FStar_TypeChecker_Env.is_layered_effect
                                              env1))
                                       in
                                    if uu____7637
                                    then
                                      let uu____7643 =
                                        FStar_Syntax_Syntax.mk_Total repr  in
                                      FStar_All.pipe_right uu____7643
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
                                       let uu____7655 =
                                         FStar_Syntax_Syntax.mk_Comp ct  in
                                       FStar_All.pipe_right uu____7655
                                         FStar_TypeChecker_Common.lcomp_of_comp)
                                     in
                                  let uu____7656 =
                                    comp_check_expected_typ env1 e3 c2  in
                                  match uu____7656 with
                                  | (e4,c3,g') ->
                                      let uu____7672 =
                                        let uu____7673 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g'
                                           in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7673
                                         in
                                      (e4, c3, uu____7672))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7675;
              FStar_Syntax_Syntax.vars = uu____7676;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7724 =
               let uu____7726 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l  in
               Prims.op_Negation uu____7726  in
             if uu____7724
             then
               let uu____7729 =
                 let uu____7735 =
                   let uu____7737 = FStar_Ident.string_of_lid l  in
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     uu____7737
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7735)  in
               FStar_Errors.raise_error uu____7729 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7743 = FStar_Syntax_Util.head_and_args top  in
             match uu____7743 with
             | (reflect_op,uu____7767) ->
                 let uu____7792 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____7792 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____7813 =
                        let uu____7819 =
                          let uu____7821 = FStar_Ident.string_of_lid l  in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7821
                           in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7819)  in
                      FStar_Errors.raise_error uu____7813
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____7843 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____7843 with
                       | (env_no_ex,uu____7857) ->
                           let uu____7862 =
                             let uu____7871 =
                               tc_tot_or_gtot_term env_no_ex e1  in
                             match uu____7871 with
                             | (e2,c,g) ->
                                 ((let uu____7890 =
                                     let uu____7892 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c
                                        in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7892
                                      in
                                   if uu____7890
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g))
                              in
                           (match uu____7862 with
                            | (e2,c_e,g_e) ->
                                let uu____7930 =
                                  let uu____7945 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____7945 with
                                  | (a,u_a) ->
                                      let uu____7966 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a
                                         in
                                      (match uu____7966 with
                                       | (a_uvar,uu____7995,g_a) ->
                                           let uu____8009 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar
                                              in
                                           (uu____8009, u_a, a_uvar, g_a))
                                   in
                                (match uu____7930 with
                                 | ((expected_repr_typ,g_repr),u_a,a,g_a) ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ
                                        in
                                     let eff_args =
                                       let uu____8051 =
                                         let uu____8052 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ
                                            in
                                         uu____8052.FStar_Syntax_Syntax.n  in
                                       match uu____8051 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8065,uu____8066::args) ->
                                           args
                                       | uu____8108 ->
                                           let uu____8109 =
                                             let uu____8115 =
                                               let uu____8117 =
                                                 FStar_Ident.string_of_lid l
                                                  in
                                               let uu____8119 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ
                                                  in
                                               let uu____8121 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ
                                                  in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____8117 uu____8119
                                                 uu____8121
                                                in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____8115)
                                              in
                                           FStar_Errors.raise_error
                                             uu____8109
                                             top.FStar_Syntax_Syntax.pos
                                        in
                                     let c =
                                       let uu____8136 =
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
                                       FStar_All.pipe_right uu____8136
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____8172 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____8172 with
                                      | (e4,c1,g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_TypeChecker_Common.eff_name),
                                                        (c1.FStar_TypeChecker_Common.res_typ)))))
                                              e4.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____8195 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g']
                                             in
                                          (e5, c1, uu____8195))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8234 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8234 with
            | (head1,args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head,(uu____8284,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____8285))::(tau,FStar_Pervasives_Native.None
                                                               )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8338 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8338 with
            | (head1,args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8413 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8623 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____8413 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let env0 = env1  in
           let env2 =
             let uu____8742 =
               let uu____8743 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____8743 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____8742 instantiate_both  in
           ((let uu____8759 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____8759
             then
               let uu____8762 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____8764 = FStar_Syntax_Print.term_to_string top  in
               let uu____8766 =
                 let uu____8768 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____8768
                   (fun uu___3_8775  ->
                      match uu___3_8775 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8762
                 uu____8764 uu____8766
             else ());
            (let uu____8784 = tc_term (no_inst env2) head  in
             match uu____8784 with
             | (head1,chead,g_head) ->
                 let uu____8800 =
                   let uu____8805 = FStar_TypeChecker_Common.lcomp_comp chead
                      in
                   FStar_All.pipe_right uu____8805
                     (fun uu____8822  ->
                        match uu____8822 with
                        | (c,g) ->
                            let uu____8833 =
                              FStar_TypeChecker_Env.conj_guard g_head g  in
                            (c, uu____8833))
                    in
                 (match uu____8800 with
                  | (chead1,g_head1) ->
                      let uu____8842 =
                        let uu____8849 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8852 = FStar_Options.lax ()  in
                              Prims.op_Negation uu____8852))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head1)
                           in
                        if uu____8849
                        then
                          let uu____8861 =
                            let uu____8868 =
                              FStar_TypeChecker_Env.expected_typ env0  in
                            check_short_circuit_args env2 head1 chead1
                              g_head1 args uu____8868
                             in
                          match uu____8861 with | (e1,c,g) -> (e1, c, g)
                        else
                          (let uu____8882 =
                             FStar_TypeChecker_Env.expected_typ env0  in
                           check_application_args env2 head1 chead1 g_head1
                             args uu____8882)
                         in
                      (match uu____8842 with
                       | (e1,c,g) ->
                           let uu____8894 =
                             let uu____8901 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c
                                in
                             if uu____8901
                             then
                               let uu____8910 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ
                                  in
                               match uu____8910 with
                               | (e2,res_typ,implicits) ->
                                   let uu____8926 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ
                                      in
                                   (e2, uu____8926, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard)
                              in
                           (match uu____8894 with
                            | (e2,c1,implicits) ->
                                ((let uu____8939 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme
                                     in
                                  if uu____8939
                                  then
                                    let uu____8942 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g
                                       in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8942
                                  else ());
                                 (let uu____8947 =
                                    comp_check_expected_typ env0 e2 c1  in
                                  match uu____8947 with
                                  | (e3,c2,g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits
                                         in
                                      ((let uu____8966 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme
                                           in
                                        if uu____8966
                                        then
                                          let uu____8969 =
                                            FStar_Syntax_Print.term_to_string
                                              e3
                                             in
                                          let uu____8971 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1
                                             in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8969 uu____8971
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8976 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8999;
                FStar_Syntax_Syntax.lbunivs = uu____9000;
                FStar_Syntax_Syntax.lbtyp = uu____9001;
                FStar_Syntax_Syntax.lbeff = uu____9002;
                FStar_Syntax_Syntax.lbdef = uu____9003;
                FStar_Syntax_Syntax.lbattrs = uu____9004;
                FStar_Syntax_Syntax.lbpos = uu____9005;_}::[]),uu____9006)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____9032),uu____9033) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9051;
                FStar_Syntax_Syntax.lbunivs = uu____9052;
                FStar_Syntax_Syntax.lbtyp = uu____9053;
                FStar_Syntax_Syntax.lbeff = uu____9054;
                FStar_Syntax_Syntax.lbdef = uu____9055;
                FStar_Syntax_Syntax.lbattrs = uu____9056;
                FStar_Syntax_Syntax.lbpos = uu____9057;_}::uu____9058),uu____9059)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____9087),uu____9088) ->
           check_inner_let_rec env1 top)

and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let uu____9114 =
        let uu____9115 = FStar_Syntax_Subst.compress top  in
        uu____9115.FStar_Syntax_Syntax.n  in
      match uu____9114 with
      | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
          let uu____9162 = FStar_TypeChecker_Env.clear_expected_typ env  in
          (match uu____9162 with
           | (env1,topt) ->
               let env11 = instantiate_both env1  in
               let uu____9182 = tc_term env11 e1  in
               (match uu____9182 with
                | (e11,c1,g1) ->
                    let uu____9198 =
                      let uu____9209 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1  in
                      match uu____9209 with
                      | FStar_Pervasives_Native.Some (e12,c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None  -> (e11, c1, eqns)  in
                    (match uu____9198 with
                     | (e12,c11,eqns1) ->
                         let eqns2 = eqns1  in
                         let uu____9264 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None  ->
                               let uu____9278 = FStar_Syntax_Util.type_u ()
                                  in
                               (match uu____9278 with
                                | (k,uu____9290) ->
                                    let uu____9291 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k
                                       in
                                    (match uu____9291 with
                                     | (res_t,uu____9312,g) ->
                                         let uu____9326 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t
                                            in
                                         let uu____9327 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g
                                            in
                                         (uu____9326, res_t, uu____9327)))
                            in
                         (match uu____9264 with
                          | (env_branches,res_t,g11) ->
                              ((let uu____9338 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme
                                   in
                                if uu____9338
                                then
                                  let uu____9341 =
                                    FStar_Syntax_Print.term_to_string res_t
                                     in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____9341
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
                                let uu____9449 =
                                  let uu____9457 =
                                    FStar_List.fold_right
                                      (fun uu____9550  ->
                                         fun uu____9551  ->
                                           match (uu____9550, uu____9551)
                                           with
                                           | ((branch,f,eff_label,cflags,c,g,erasable_branch),
                                              (caccum,gaccum,erasable)) ->
                                               let uu____9823 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum
                                                  in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9823,
                                                 (erasable || erasable_branch)))
                                      t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false)
                                     in
                                  match uu____9457 with
                                  | (cases,g,erasable) ->
                                      let uu____9937 =
                                        FStar_TypeChecker_Util.bind_cases env
                                          res_t cases guard_x
                                         in
                                      (uu____9937, g, erasable)
                                   in
                                match uu____9449 with
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
                                        let uu____9957 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c
                                           in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9957
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres  in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____10099  ->
                                                  match uu____10099 with
                                                  | ((pat,wopt,br),uu____10147,eff_label,uu____10149,uu____10150,uu____10151,uu____10152)
                                                      ->
                                                      let uu____10191 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t
                                                         in
                                                      (pat, wopt,
                                                        uu____10191)))
                                           in
                                        let e =
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_match
                                               (scrutinee, branches))
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
                                          e2.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____10258 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name
                                         in
                                      if uu____10258
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____10266 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x
                                              in
                                           mk_match uu____10266  in
                                         let lb =
                                           let uu____10270 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name
                                              in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____10270 e12 []
                                             e12.FStar_Syntax_Syntax.pos
                                            in
                                         let e =
                                           let uu____10276 =
                                             let uu____10277 =
                                               let uu____10291 =
                                                 let uu____10294 =
                                                   let uu____10295 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       guard_x
                                                      in
                                                   [uu____10295]  in
                                                 FStar_Syntax_Subst.close
                                                   uu____10294 e_match
                                                  in
                                               ((false, [lb]), uu____10291)
                                                in
                                             FStar_Syntax_Syntax.Tm_let
                                               uu____10277
                                              in
                                           FStar_Syntax_Syntax.mk uu____10276
                                             top.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ)
                                       in
                                    ((let uu____10328 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme
                                         in
                                      if uu____10328
                                      then
                                        let uu____10331 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let uu____10333 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1
                                           in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____10331 uu____10333
                                      else ());
                                     (let uu____10338 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches
                                         in
                                      (e, cres1, uu____10338)))))))))
      | uu____10339 ->
          let uu____10340 =
            let uu____10342 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format1 "tc_match called on %s\n" uu____10342  in
          failwith uu____10340

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
          let uu____10367 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____10406))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____10447 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____10367 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____10480 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____10480 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____10484 =
                           FStar_TypeChecker_Env.get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____10484)
                 in
              let uu____10487 =
                let uu____10494 =
                  let uu____10495 =
                    let uu____10496 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____10496
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____10495  in
                tc_term uu____10494 typ  in
              (match uu____10487 with
               | (typ1,uu____10512,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____10515 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau
                        in
                     match uu____10515 with
                     | (tau1,uu____10529,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1342_10534 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1342_10534.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1342_10534.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____10536 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____10536
                            then
                              let uu____10541 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____10541
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10547 =
                              let uu____10548 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10548
                               in
                            (t, uu____10547,
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
            let uu___1352_10554 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1352_10554.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1352_10554.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1352_10554.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1352_10554.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1352_10554.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1352_10554.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1352_10554.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1352_10554.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1352_10554.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1352_10554.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1352_10554.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1352_10554.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1352_10554.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1352_10554.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1352_10554.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1352_10554.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1352_10554.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1352_10554.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1352_10554.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1352_10554.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1352_10554.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1352_10554.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1352_10554.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1352_10554.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1352_10554.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1352_10554.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1352_10554.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1352_10554.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1352_10554.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1352_10554.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1352_10554.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1352_10554.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1352_10554.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1352_10554.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1352_10554.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1352_10554.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1352_10554.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1352_10554.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1352_10554.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1352_10554.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1352_10554.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1352_10554.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1352_10554.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1352_10554.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1352_10554.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___1352_10554.FStar_TypeChecker_Env.enable_defer_to_tac)
            }  in
          let uu____10556 = FStar_Syntax_Syntax.t_tac_of a b  in
          tc_check_tot_or_gtot_term env1 tau uu____10556 ""

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
          let uu____10579 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic
             in
          (match uu____10579 with
           | (tactic1,uu____10593,g) ->
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
        let uu____10646 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____10646 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____10667 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____10667
              then FStar_Util.Inl t1
              else
                (let uu____10676 =
                   let uu____10677 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____10677
                    in
                 FStar_Util.Inr uu____10676)
               in
            let is_data_ctor uu___4_10686 =
              match uu___4_10686 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10691) -> true
              | uu____10699 -> false  in
            let uu____10703 =
              (is_data_ctor dc) &&
                (let uu____10706 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____10706)
               in
            if uu____10703
            then
              let uu____10715 =
                let uu____10721 =
                  let uu____10723 =
                    FStar_Ident.string_of_lid v.FStar_Syntax_Syntax.v  in
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    uu____10723
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10721)  in
              let uu____10727 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____10715 uu____10727
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10745 =
            let uu____10751 =
              let uu____10753 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10753
               in
            (FStar_Errors.Error_IllScopedTerm, uu____10751)  in
          FStar_Errors.raise_error uu____10745 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____10781 =
            let uu____10786 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____10786  in
          value_check_expected_typ env1 e uu____10781
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____10788 =
            let uu____10801 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____10801 with
            | FStar_Pervasives_Native.None  ->
                let uu____10816 = FStar_Syntax_Util.type_u ()  in
                (match uu____10816 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____10788 with
           | (t,uu____10854,g0) ->
               let uu____10868 =
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize_refinement
                     FStar_TypeChecker_Normalize.whnf_steps env1 t
                    in
                 let uu____10882 =
                   let uu____10883 = FStar_Syntax_Subst.compress t_norm  in
                   uu____10883.FStar_Syntax_Syntax.n  in
                 match uu____10882 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.unit_lid
                     ->
                     let uu____10899 =
                       FStar_Syntax_Syntax.unit_const_with_range r  in
                     (uu____10899, [], FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Syntax_Syntax.Tm_refine (b,phi) when
                     FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                     let uu____10916 = FStar_Syntax_Subst.open_term_bv b phi
                        in
                     (match uu____10916 with
                      | (b1,phi1) ->
                          let e1 =
                            FStar_Syntax_Syntax.unit_const_with_range r  in
                          let uu____10936 =
                            let uu____10937 =
                              let uu____10938 =
                                FStar_All.pipe_right phi1
                                  (FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (b1, e1)])
                                 in
                              FStar_All.pipe_right uu____10938
                                (fun uu____10941  ->
                                   FStar_TypeChecker_Common.NonTrivial
                                     uu____10941)
                               in
                            FStar_All.pipe_right uu____10937
                              FStar_TypeChecker_Env.guard_of_guard_formula
                             in
                          (e1, [], uu____10936))
                 | uu____10952 ->
                     let uu____10953 =
                       let uu____10955 = FStar_Range.string_of_range r  in
                       Prims.op_Hat "user-provided implicit term at "
                         uu____10955
                        in
                     FStar_TypeChecker_Util.new_implicit_var uu____10953 r
                       env1 t
                  in
               (match uu____10868 with
                | (e1,uu____10965,g1) ->
                    let uu____10979 =
                      let uu____10980 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____10980
                        FStar_TypeChecker_Common.lcomp_of_comp
                       in
                    let uu____10981 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____10979, uu____10981)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10983 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10993 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____10993)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____10983 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1430_11007 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1430_11007.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1430_11007.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____11010 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____11010 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____11031 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____11031
                       then FStar_Util.Inl t1
                       else
                         (let uu____11040 =
                            let uu____11041 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____11041
                             in
                          FStar_Util.Inr uu____11040)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____11043;
             FStar_Syntax_Syntax.vars = uu____11044;_},uu____11045)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____11050 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____11050
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____11060 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____11060
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____11070;
             FStar_Syntax_Syntax.vars = uu____11071;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____11080 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____11080 with
           | ((us',t),range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range  in
               (maybe_warn_on_use env1 fv1;
                if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____11106 =
                     let uu____11112 =
                       let uu____11114 = FStar_Syntax_Print.fv_to_string fv1
                          in
                       let uu____11116 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____11118 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____11114 uu____11116 uu____11118
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____11112)
                      in
                   let uu____11122 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____11106 uu____11122)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____11141 -> failwith "Impossible") us' us1;
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____11145 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____11145 us1  in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_uinst (uu____11146,us) ->
          let uu____11152 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
              "Universe applications are only allowed on top-level identifiers")
            uu____11152
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____11162 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____11162 with
           | ((us,t),range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range  in
               (maybe_warn_on_use env1 fv1;
                (let uu____11187 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____11187
                 then
                   let uu____11192 =
                     let uu____11194 = FStar_Syntax_Syntax.lid_of_fv fv1  in
                     FStar_Syntax_Print.lid_to_string uu____11194  in
                   let uu____11195 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____11197 = FStar_Range.string_of_range range  in
                   let uu____11199 = FStar_Range.string_of_use_range range
                      in
                   let uu____11201 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____11192 uu____11195 uu____11197 uu____11199
                     uu____11201
                 else ());
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____11208 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____11208 us  in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____11236 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____11236 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____11250 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11250 with
                | (env2,uu____11264) ->
                    let uu____11269 = tc_binders env2 bs1  in
                    (match uu____11269 with
                     | (bs2,env3,g,us) ->
                         let uu____11288 = tc_comp env3 c1  in
                         (match uu____11288 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1516_11307 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1516_11307.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1516_11307.FStar_Syntax_Syntax.vars)
                                }  in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us)
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    top.FStar_Syntax_Syntax.pos
                                   in
                                let g1 =
                                  let uu____11318 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____11318
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
              top.FStar_Syntax_Syntax.pos
             in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              top.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____11335 =
            let uu____11340 =
              let uu____11341 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11341]  in
            FStar_Syntax_Subst.open_term uu____11340 phi  in
          (match uu____11335 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____11369 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11369 with
                | (env2,uu____11383) ->
                    let uu____11388 =
                      let uu____11403 = FStar_List.hd x1  in
                      tc_binder env2 uu____11403  in
                    (match uu____11388 with
                     | (x2,env3,f1,u) ->
                         ((let uu____11439 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____11439
                           then
                             let uu____11442 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____11444 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11446 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____11442 uu____11444 uu____11446
                           else ());
                          (let uu____11453 = FStar_Syntax_Util.type_u ()  in
                           match uu____11453 with
                           | (t_phi,uu____11465) ->
                               let uu____11466 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                   "refinement formula must be pure or ghost"
                                  in
                               (match uu____11466 with
                                | (phi2,uu____11481,f2) ->
                                    let e1 =
                                      let uu___1554_11486 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1554_11486.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1554_11486.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____11495 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____11495
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____11524) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____11551 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____11551
            then
              let uu____11554 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1567_11558 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1567_11558.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1567_11558.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____11554
            else ());
           (let uu____11574 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____11574 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____11587 ->
          let uu____11588 =
            let uu____11590 = FStar_Syntax_Print.term_to_string top  in
            let uu____11592 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____11590
              uu____11592
             in
          failwith uu____11588

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
          | FStar_Const.Const_bool uu____11605 -> FStar_Syntax_Util.t_bool
          | FStar_Const.Const_int (uu____11607,FStar_Pervasives_Native.None )
              -> FStar_Syntax_Syntax.t_int
          | FStar_Const.Const_int
              (uu____11620,FStar_Pervasives_Native.Some msize) ->
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
          | FStar_Const.Const_string uu____11638 ->
              FStar_Syntax_Syntax.t_string
          | FStar_Const.Const_real uu____11644 -> FStar_Syntax_Syntax.t_real
          | FStar_Const.Const_float uu____11646 ->
              FStar_Syntax_Syntax.t_float
          | FStar_Const.Const_char uu____11647 ->
              let uu____11649 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____11649 FStar_Util.must
          | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
          | FStar_Const.Const_range uu____11654 ->
              FStar_Syntax_Syntax.t_range
          | FStar_Const.Const_range_of  ->
              let uu____11655 =
                let uu____11661 =
                  let uu____11663 = FStar_Parser_Const.const_to_string c  in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11663
                   in
                (FStar_Errors.Fatal_IllTyped, uu____11661)  in
              FStar_Errors.raise_error uu____11655 r
          | FStar_Const.Const_set_range_of  ->
              let uu____11667 =
                let uu____11673 =
                  let uu____11675 = FStar_Parser_Const.const_to_string c  in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11675
                   in
                (FStar_Errors.Fatal_IllTyped, uu____11673)  in
              FStar_Errors.raise_error uu____11667 r
          | FStar_Const.Const_reify  ->
              let uu____11679 =
                let uu____11685 =
                  let uu____11687 = FStar_Parser_Const.const_to_string c  in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11687
                   in
                (FStar_Errors.Fatal_IllTyped, uu____11685)  in
              FStar_Errors.raise_error uu____11679 r
          | FStar_Const.Const_reflect uu____11691 ->
              let uu____11692 =
                let uu____11698 =
                  let uu____11700 = FStar_Parser_Const.const_to_string c  in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11700
                   in
                (FStar_Errors.Fatal_IllTyped, uu____11698)  in
              FStar_Errors.raise_error uu____11692 r
          | uu____11704 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____11723) ->
          let uu____11732 = FStar_Syntax_Util.type_u ()  in
          (match uu____11732 with
           | (k,u) ->
               let uu____11745 = tc_check_tot_or_gtot_term env t k ""  in
               (match uu____11745 with
                | (t1,uu____11760,g) ->
                    let uu____11762 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11762, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____11764) ->
          let uu____11773 = FStar_Syntax_Util.type_u ()  in
          (match uu____11773 with
           | (k,u) ->
               let uu____11786 = tc_check_tot_or_gtot_term env t k ""  in
               (match uu____11786 with
                | (t1,uu____11801,g) ->
                    let uu____11803 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11803, u, g)))
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
                  c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____11811 =
              let uu____11812 =
                FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ
                 in
              uu____11812 :: (c1.FStar_Syntax_Syntax.effect_args)  in
            FStar_Syntax_Syntax.mk_Tm_app head1 uu____11811
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____11829 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff ""  in
          (match uu____11829 with
           | (tc1,uu____11844,f) ->
               let uu____11846 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____11846 with
                | (head2,args) ->
                    let comp_univs =
                      let uu____11896 =
                        let uu____11897 = FStar_Syntax_Subst.compress head2
                           in
                        uu____11897.FStar_Syntax_Syntax.n  in
                      match uu____11896 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11900,us) -> us
                      | uu____11906 -> []  in
                    let uu____11907 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____11907 with
                     | (uu____11930,args1) ->
                         let uu____11956 =
                           let uu____11979 = FStar_List.hd args1  in
                           let uu____11996 = FStar_List.tl args1  in
                           (uu____11979, uu____11996)  in
                         (match uu____11956 with
                          | (res,args2) ->
                              let uu____12077 =
                                let uu____12086 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_12114  ->
                                          match uu___5_12114 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____12122 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____12122 with
                                               | (env1,uu____12134) ->
                                                   let uu____12139 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____12139 with
                                                    | (e1,uu____12151,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____12086
                                  FStar_List.unzip
                                 in
                              (match uu____12077 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1697_12192 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1697_12192.FStar_Syntax_Syntax.effect_name);
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
                                   let uu____12198 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____12198))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____12208 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____12212 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____12224 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____12224
        | FStar_Syntax_Syntax.U_max us ->
            let uu____12228 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____12228
        | FStar_Syntax_Syntax.U_name x ->
            let uu____12232 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____12232
            then u2
            else
              (let uu____12237 =
                 let uu____12239 =
                   let uu____12241 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____12241 " not found"  in
                 Prims.op_Hat "Universe variable " uu____12239  in
               failwith uu____12237)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____12248 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____12248 FStar_Pervasives_Native.snd
         | uu____12257 -> aux u)

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
                | uu____12292 ->
                    failwith
                      "Impossible: Can't have a let rec annotation but no expected type");
               (let uu____12305 = tc_binders env bs  in
                match uu____12305 with
                | (bs1,envbody,g_env,uu____12335) ->
                    (FStar_Pervasives_Native.None, bs1, [],
                      FStar_Pervasives_Native.None, envbody, body, g_env)))
          | FStar_Pervasives_Native.Some t ->
              let t1 = FStar_Syntax_Subst.compress t  in
              let rec as_function_typ norm1 t2 =
                let uu____12381 =
                  let uu____12382 = FStar_Syntax_Subst.compress t2  in
                  uu____12382.FStar_Syntax_Syntax.n  in
                match uu____12381 with
                | FStar_Syntax_Syntax.Tm_uvar uu____12405 ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____12428 -> failwith "Impossible");
                     (let uu____12441 = tc_binders env bs  in
                      match uu____12441 with
                      | (bs1,envbody,g_env,uu____12473) ->
                          let uu____12474 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody
                             in
                          (match uu____12474 with
                           | (envbody1,uu____12502) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12513;
                       FStar_Syntax_Syntax.pos = uu____12514;
                       FStar_Syntax_Syntax.vars = uu____12515;_},uu____12516)
                    ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____12563 -> failwith "Impossible");
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
                             let uu___1828_13318 = envbody  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1828_13318.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1828_13318.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1828_13318.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1828_13318.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1828_13318.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1828_13318.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1828_13318.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1828_13318.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1828_13318.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1828_13318.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1828_13318.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1828_13318.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1828_13318.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs = [];
                               FStar_TypeChecker_Env.top_level =
                                 (uu___1828_13318.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1828_13318.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___1828_13318.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (uu___1828_13318.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1828_13318.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1828_13318.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1828_13318.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1828_13318.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1828_13318.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1828_13318.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1828_13318.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1828_13318.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1828_13318.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1828_13318.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1828_13318.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1828_13318.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1828_13318.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1828_13318.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1828_13318.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1828_13318.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1828_13318.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1828_13318.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1828_13318.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1828_13318.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1828_13318.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1828_13318.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1828_13318.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1828_13318.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1828_13318.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1828_13318.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1828_13318.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1828_13318.FStar_TypeChecker_Env.erasable_types_tab);
                               FStar_TypeChecker_Env.enable_defer_to_tac =
                                 (uu___1828_13318.FStar_TypeChecker_Env.enable_defer_to_tac)
                             }  in
                           let uu____13328 =
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____13394  ->
                                     fun uu____13395  ->
                                       match (uu____13394, uu____13395) with
                                       | ((env1,letrec_binders,g),(l,t3,u_names))
                                           ->
                                           let uu____13486 =
                                             let uu____13493 =
                                               let uu____13494 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____13494
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____13493 t3  in
                                           (match uu____13486 with
                                            | (t4,uu____13518,g') ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env1 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____13531 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___1846_13534
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___1846_13534.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___1846_13534.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____13531 ::
                                                        letrec_binders
                                                  | uu____13535 ->
                                                      letrec_binders
                                                   in
                                                let uu____13540 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g'
                                                   in
                                                (env2, lb, uu____13540)))
                                  (envbody1, [],
                                    FStar_TypeChecker_Env.trivial_guard))
                              in
                           match uu____13328 with
                           | (envbody2,letrec_binders,g) ->
                               let uu____13560 =
                                 FStar_TypeChecker_Env.close_guard envbody2
                                   bs1 g
                                  in
                               (envbody2, letrec_binders, uu____13560)
                            in
                         let envbody =
                           let uu___1854_13564 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1854_13564.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1854_13564.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1854_13564.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1854_13564.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1854_13564.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1854_13564.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1854_13564.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1854_13564.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1854_13564.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1854_13564.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1854_13564.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1854_13564.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1854_13564.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs = [];
                             FStar_TypeChecker_Env.top_level =
                               (uu___1854_13564.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1854_13564.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1854_13564.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1854_13564.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1854_13564.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1854_13564.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___1854_13564.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1854_13564.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1854_13564.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1854_13564.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1854_13564.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1854_13564.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1854_13564.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1854_13564.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1854_13564.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1854_13564.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1854_13564.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1854_13564.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1854_13564.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1854_13564.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1854_13564.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1854_13564.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1854_13564.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1854_13564.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1854_13564.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1854_13564.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1854_13564.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1854_13564.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1854_13564.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1854_13564.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1854_13564.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1854_13564.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1854_13564.FStar_TypeChecker_Env.enable_defer_to_tac)
                           }  in
                         let uu____13574 =
                           check_actuals_against_formals envbody bs
                             bs_expected1 body
                            in
                         (match uu____13574 with
                          | (envbody1,bs1,g_env,c,body1) ->
                              let envbody2 =
                                let uu___1863_13611 = envbody1  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1863_13611.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1863_13611.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1863_13611.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___1863_13611.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1863_13611.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___1863_13611.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1863_13611.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1863_13611.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1863_13611.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1863_13611.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1863_13611.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1863_13611.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1863_13611.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (env.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1863_13611.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1863_13611.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1863_13611.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1863_13611.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1863_13611.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1863_13611.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1863_13611.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1863_13611.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1863_13611.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1863_13611.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1863_13611.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1863_13611.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1863_13611.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1863_13611.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1863_13611.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1863_13611.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1863_13611.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1863_13611.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1863_13611.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1863_13611.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1863_13611.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1863_13611.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1863_13611.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1863_13611.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1863_13611.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1863_13611.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1863_13611.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1863_13611.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1863_13611.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1863_13611.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1863_13611.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1863_13611.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1863_13611.FStar_TypeChecker_Env.enable_defer_to_tac)
                                }  in
                              let uu____13612 = mk_letrec_env envbody2 bs1 c
                                 in
                              (match uu____13612 with
                               | (envbody3,letrecs,g_annots) ->
                                   let envbody4 =
                                     FStar_TypeChecker_Env.set_expected_typ
                                       envbody3
                                       (FStar_Syntax_Util.comp_result c)
                                      in
                                   let uu____13649 =
                                     FStar_TypeChecker_Env.conj_guard g_env
                                       g_annots
                                      in
                                   ((FStar_Pervasives_Native.Some t2), bs1,
                                     letrecs,
                                     (FStar_Pervasives_Native.Some c),
                                     envbody4, body1, uu____13649))))
                | uu____13656 ->
                    if Prims.op_Negation norm1
                    then
                      let uu____13678 =
                        let uu____13679 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.unfold_whnf env)
                           in
                        FStar_All.pipe_right uu____13679
                          FStar_Syntax_Util.unascribe
                         in
                      as_function_typ true uu____13678
                    else
                      (let uu____13683 =
                         tc_abs_expected_function_typ env bs
                           FStar_Pervasives_Native.None body
                          in
                       match uu____13683 with
                       | (uu____13722,bs1,uu____13724,c_opt,envbody,body1,g_env)
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
        let rec aux uu____13798 bs1 bs_expected1 =
          match uu____13798 with
          | (env1,subst) ->
              (match (bs1, bs_expected1) with
               | ([],[]) ->
                   (env1, [], FStar_Pervasives_Native.None,
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ((uu____13905,FStar_Pervasives_Native.None )::uu____13906,
                  (hd_e,q)::uu____13909) when
                   FStar_Syntax_Syntax.is_implicit_or_meta q ->
                   let bv =
                     let uu____13961 =
                       let uu____13964 =
                         FStar_Ident.range_of_id
                           hd_e.FStar_Syntax_Syntax.ppname
                          in
                       FStar_Pervasives_Native.Some uu____13964  in
                     let uu____13965 =
                       FStar_Syntax_Subst.subst subst
                         hd_e.FStar_Syntax_Syntax.sort
                        in
                     FStar_Syntax_Syntax.new_bv uu____13961 uu____13965  in
                   aux (env1, subst) ((bv, q) :: bs1) bs_expected1
               | ((hd,imp)::bs2,(hd_expected,imp')::bs_expected2) ->
                   ((let special q1 q2 =
                       match (q1, q2) with
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta
                          uu____14060),FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____14061)) -> true
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Equality )) -> true
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit
                          uu____14072),FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____14073)) -> true
                       | uu____14080 -> false  in
                     let uu____14090 =
                       (Prims.op_Negation (special imp imp')) &&
                         (let uu____14093 =
                            FStar_Syntax_Util.eq_aqual imp imp'  in
                          uu____14093 <> FStar_Syntax_Util.Equal)
                        in
                     if uu____14090
                     then
                       let uu____14095 =
                         let uu____14101 =
                           let uu____14103 =
                             FStar_Syntax_Print.bv_to_string hd  in
                           FStar_Util.format1
                             "Inconsistent implicit argument annotation on argument %s"
                             uu____14103
                            in
                         (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                           uu____14101)
                          in
                       let uu____14107 = FStar_Syntax_Syntax.range_of_bv hd
                          in
                       FStar_Errors.raise_error uu____14095 uu____14107
                     else ());
                    (let expected_t =
                       FStar_Syntax_Subst.subst subst
                         hd_expected.FStar_Syntax_Syntax.sort
                        in
                     let uu____14111 =
                       let uu____14118 =
                         let uu____14119 =
                           FStar_Syntax_Util.unmeta
                             hd.FStar_Syntax_Syntax.sort
                            in
                         uu____14119.FStar_Syntax_Syntax.n  in
                       match uu____14118 with
                       | FStar_Syntax_Syntax.Tm_unknown  ->
                           (expected_t, FStar_TypeChecker_Env.trivial_guard)
                       | uu____14130 ->
                           ((let uu____14132 =
                               FStar_TypeChecker_Env.debug env1
                                 FStar_Options.High
                                in
                             if uu____14132
                             then
                               let uu____14135 =
                                 FStar_Syntax_Print.bv_to_string hd  in
                               FStar_Util.print1 "Checking binder %s\n"
                                 uu____14135
                             else ());
                            (let uu____14140 =
                               tc_tot_or_gtot_term env1
                                 hd.FStar_Syntax_Syntax.sort
                                in
                             match uu____14140 with
                             | (t,uu____14154,g1_env) ->
                                 let g2_env =
                                   let uu____14157 =
                                     FStar_TypeChecker_Rel.teq_nosmt env1 t
                                       expected_t
                                      in
                                   match uu____14157 with
                                   | FStar_Pervasives_Native.Some g ->
                                       FStar_All.pipe_right g
                                         (FStar_TypeChecker_Rel.resolve_implicits
                                            env1)
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____14161 =
                                         FStar_TypeChecker_Rel.get_subtyping_prop
                                           env1 expected_t t
                                          in
                                       (match uu____14161 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____14164 =
                                              FStar_TypeChecker_Err.basic_type_error
                                                env1
                                                FStar_Pervasives_Native.None
                                                expected_t t
                                               in
                                            let uu____14170 =
                                              FStar_TypeChecker_Env.get_range
                                                env1
                                               in
                                            FStar_Errors.raise_error
                                              uu____14164 uu____14170
                                        | FStar_Pervasives_Native.Some g_env
                                            ->
                                            FStar_TypeChecker_Util.label_guard
                                              (hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                              "Type annotation on parameter incompatible with the expected type"
                                              g_env)
                                    in
                                 let uu____14173 =
                                   FStar_TypeChecker_Env.conj_guard g1_env
                                     g2_env
                                    in
                                 (t, uu____14173)))
                        in
                     match uu____14111 with
                     | (t,g_env) ->
                         let hd1 =
                           let uu___1959_14199 = hd  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1959_14199.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1959_14199.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t
                           }  in
                         let b = (hd1, imp)  in
                         let b_expected = (hd_expected, imp')  in
                         let env_b = push_binding env1 b  in
                         let subst1 =
                           let uu____14222 =
                             FStar_Syntax_Syntax.bv_to_name hd1  in
                           maybe_extend_subst subst b_expected uu____14222
                            in
                         let uu____14225 =
                           aux (env_b, subst1) bs2 bs_expected2  in
                         (match uu____14225 with
                          | (env_bs,bs3,rest,g'_env_b,subst2) ->
                              let g'_env =
                                FStar_TypeChecker_Env.close_guard env_bs 
                                  [b] g'_env_b
                                 in
                              let uu____14290 =
                                FStar_TypeChecker_Env.conj_guard g_env g'_env
                                 in
                              (env_bs, (b :: bs3), rest, uu____14290, subst2))))
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
            let uu____14429 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____14429 top.FStar_Syntax_Syntax.pos
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____14437 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____14437 with
          | (env1,topt) ->
              ((let uu____14457 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____14457
                then
                  let uu____14460 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____14460
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____14474 =
                  tc_abs_expected_function_typ env1 bs topt body  in
                match uu____14474 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____14515 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____14515
                      then
                        let uu____14518 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____14523 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____14528 =
                          let uu____14530 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____14530 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____14518 uu____14523 uu____14528
                      else ());
                     (let uu____14540 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____14540
                      then
                        let uu____14545 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____14548 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____14545 uu____14548
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____14554 =
                        let uu____14565 =
                          let uu____14573 =
                            (FStar_All.pipe_right c_opt FStar_Util.is_some)
                              &&
                              (let uu____14583 =
                                 let uu____14584 =
                                   FStar_Syntax_Subst.compress body1  in
                                 uu____14584.FStar_Syntax_Syntax.n  in
                               match uu____14583 with
                               | FStar_Syntax_Syntax.Tm_app (head,args) when
                                   (FStar_List.length args) = Prims.int_one
                                   ->
                                   let uu____14624 =
                                     let uu____14625 =
                                       FStar_Syntax_Subst.compress head  in
                                     uu____14625.FStar_Syntax_Syntax.n  in
                                   (match uu____14624 with
                                    | FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reflect
                                        uu____14629) -> true
                                    | uu____14631 -> false)
                               | uu____14633 -> false)
                             in
                          if uu____14573
                          then
                            let uu____14643 =
                              let uu____14644 =
                                FStar_TypeChecker_Env.clear_expected_typ
                                  envbody1
                                 in
                              FStar_All.pipe_right uu____14644
                                FStar_Pervasives_Native.fst
                               in
                            let uu____14659 =
                              let uu____14660 =
                                let uu____14661 =
                                  let uu____14688 =
                                    let uu____14705 =
                                      let uu____14714 =
                                        FStar_All.pipe_right c_opt
                                          FStar_Util.must
                                         in
                                      FStar_Util.Inr uu____14714  in
                                    (uu____14705,
                                      FStar_Pervasives_Native.None)
                                     in
                                  (body1, uu____14688,
                                    FStar_Pervasives_Native.None)
                                   in
                                FStar_Syntax_Syntax.Tm_ascribed uu____14661
                                 in
                              FStar_Syntax_Syntax.mk uu____14660
                                FStar_Range.dummyRange
                               in
                            (uu____14643, uu____14659, false)
                          else
                            (let uu____14763 =
                               let uu____14765 =
                                 let uu____14772 =
                                   let uu____14773 =
                                     FStar_Syntax_Subst.compress body1  in
                                   uu____14773.FStar_Syntax_Syntax.n  in
                                 (c_opt, uu____14772)  in
                               match uu____14765 with
                               | (FStar_Pervasives_Native.None
                                  ,FStar_Syntax_Syntax.Tm_ascribed
                                  (uu____14779,(FStar_Util.Inr
                                                expected_c,uu____14781),uu____14782))
                                   -> false
                               | uu____14832 -> true  in
                             (envbody1, body1, uu____14763))
                           in
                        match uu____14565 with
                        | (envbody2,body2,should_check_expected_effect) ->
                            let uu____14856 =
                              tc_term
                                (let uu___2044_14865 = envbody2  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2044_14865.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2044_14865.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2044_14865.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2044_14865.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2044_14865.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2044_14865.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2044_14865.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2044_14865.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2044_14865.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2044_14865.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2044_14865.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2044_14865.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2044_14865.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2044_14865.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level = false;
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2044_14865.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___2044_14865.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2044_14865.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2044_14865.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___2044_14865.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2044_14865.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2044_14865.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2044_14865.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2044_14865.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2044_14865.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2044_14865.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2044_14865.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2044_14865.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2044_14865.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2044_14865.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2044_14865.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2044_14865.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2044_14865.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2044_14865.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2044_14865.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___2044_14865.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2044_14865.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___2044_14865.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2044_14865.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2044_14865.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2044_14865.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2044_14865.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2044_14865.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___2044_14865.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___2044_14865.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___2044_14865.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) body2
                               in
                            (match uu____14856 with
                             | (body3,cbody,guard_body) ->
                                 let guard_body1 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     envbody2 guard_body
                                    in
                                 if should_check_expected_effect
                                 then
                                   let uu____14892 =
                                     FStar_TypeChecker_Common.lcomp_comp
                                       cbody
                                      in
                                   (match uu____14892 with
                                    | (cbody1,g_lc) ->
                                        let uu____14909 =
                                          check_expected_effect
                                            (let uu___2055_14918 = envbody2
                                                in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 use_eq;
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.lax);
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.phase1);
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___2055_14918.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) c_opt (body3, cbody1)
                                           in
                                        (match uu____14909 with
                                         | (body4,cbody2,guard) ->
                                             let uu____14932 =
                                               let uu____14933 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_lc guard
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 guard_body1 uu____14933
                                                in
                                             (body4, cbody2, uu____14932)))
                                 else
                                   (let uu____14940 =
                                      FStar_TypeChecker_Common.lcomp_comp
                                        cbody
                                       in
                                    match uu____14940 with
                                    | (cbody1,g_lc) ->
                                        let uu____14957 =
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 g_lc
                                           in
                                        (body3, cbody1, uu____14957)))
                         in
                      match uu____14554 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____14980 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14983 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____14983)
                               in
                            if uu____14980
                            then
                              let uu____14986 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____14987 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____14986
                                uu____14987
                            else
                              (let guard =
                                 let uu____14991 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14991
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
                          let uu____15006 =
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
                                 | FStar_Syntax_Syntax.Tm_arrow uu____15030
                                     -> (e, t_annot, guard1)
                                 | uu____15045 ->
                                     let lc =
                                       let uu____15047 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed
                                          in
                                       FStar_All.pipe_right uu____15047
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let uu____15048 =
                                       FStar_TypeChecker_Util.check_has_type
                                         env1 e lc t1
                                        in
                                     (match uu____15048 with
                                      | (e1,uu____15062,guard') ->
                                          let uu____15064 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t_annot, uu____15064)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____15006 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____15075 =
                                 let uu____15080 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____15080 guard2
                                  in
                               (match uu____15075 with
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
              (let uu____15131 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____15131
               then
                 let uu____15134 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos
                    in
                 let uu____15136 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____15134
                   uu____15136
               else ());
              (let monadic_application uu____15218 subst arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____15218 with
                 | (head1,chead1,ghead1,cres) ->
                     let uu____15287 =
                       check_no_escape (FStar_Pervasives_Native.Some head1)
                         env fvs (FStar_Syntax_Util.comp_result cres)
                        in
                     (match uu____15287 with
                      | (rt,g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt  in
                          let uu____15301 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____15317 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____15317
                                   in
                                (cres1, g)
                            | uu____15318 ->
                                let g =
                                  let uu____15328 =
                                    let uu____15329 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____15329
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____15328
                                   in
                                let uu____15330 =
                                  let uu____15331 =
                                    FStar_Syntax_Util.arrow bs cres1  in
                                  FStar_Syntax_Syntax.mk_Total uu____15331
                                   in
                                (uu____15330, g)
                             in
                          (match uu____15301 with
                           | (cres2,guard1) ->
                               ((let uu____15341 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium
                                    in
                                 if uu____15341
                                 then
                                   let uu____15344 =
                                     FStar_Syntax_Print.comp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____15344
                                 else ());
                                (let uu____15349 =
                                   let uu____15354 =
                                     let uu____15355 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         chead1
                                        in
                                     FStar_All.pipe_right uu____15355
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   let uu____15356 =
                                     let uu____15357 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         cres2
                                        in
                                     FStar_All.pipe_right uu____15357
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   (uu____15354, uu____15356)  in
                                 match uu____15349 with
                                 | (chead2,cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____15381  ->
                                                 match uu____15381 with
                                                 | (uu____15391,uu____15392,lc)
                                                     ->
                                                     (let uu____15400 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc
                                                         in
                                                      Prims.op_Negation
                                                        uu____15400)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev)
                                          in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head1
                                           (FStar_List.rev arg_rets_rev)
                                           head1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____15411 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful
                                          in
                                       if uu____15411
                                       then
                                         ((let uu____15415 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15415
                                           then
                                             let uu____15418 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____15418
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____15426 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15426
                                           then
                                             let uu____15429 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____15429
                                           else ());
                                          cres3)
                                        in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c  ->
                                            fun uu____15460  ->
                                              match uu____15460 with
                                              | ((e,q),x,c) ->
                                                  ((let uu____15502 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15502
                                                    then
                                                      let uu____15505 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                             -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1
                                                         in
                                                      let uu____15510 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15512 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____15505
                                                        uu____15510
                                                        uu____15512
                                                    else ());
                                                   (let uu____15517 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15517
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
                                       (let uu____15528 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____15528
                                        then
                                          let uu____15531 =
                                            FStar_Syntax_Print.term_to_string
                                              head1
                                             in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____15531
                                        else ());
                                       (let uu____15536 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2
                                           in
                                        if uu____15536
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
                                       let uu____15547 =
                                         let uu____15548 =
                                           FStar_Syntax_Subst.compress head1
                                            in
                                         uu____15548.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15547 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____15553 -> false  in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1  ->
                                                fun uu____15576  ->
                                                  match uu____15576 with
                                                  | (arg,uu____15590,uu____15591)
                                                      -> arg :: args1) []
                                             arg_comps_rev
                                            in
                                         let app =
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             head1 args1 r
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
                                         (let uu____15600 =
                                            let map_fun uu____15666 =
                                              match uu____15666 with
                                              | ((e,q),uu____15707,c) ->
                                                  ((let uu____15730 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15730
                                                    then
                                                      let uu____15733 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15735 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____15733
                                                        uu____15735
                                                    else ());
                                                   (let uu____15740 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15740
                                                    then
                                                      ((let uu____15766 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15766
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
                                                           (let uu____15807 =
                                                              let uu____15809
                                                                =
                                                                let uu____15810
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head1
                                                                   in
                                                                uu____15810.FStar_Syntax_Syntax.n
                                                                 in
                                                              match uu____15809
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____15815
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore"
                                                                     in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____15815
                                                              | uu____15817
                                                                  -> true
                                                               in
                                                            Prims.op_Negation
                                                              uu____15807)
                                                          in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____15821 =
                                                            let uu____15827 =
                                                              let uu____15829
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e
                                                                 in
                                                              let uu____15831
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  c.FStar_TypeChecker_Common.eff_name
                                                                 in
                                                              let uu____15833
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____15829
                                                                uu____15831
                                                                uu____15833
                                                               in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____15827)
                                                             in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____15821)
                                                       else ();
                                                       (let uu____15840 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15840
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
                                                        let uu____15848 =
                                                          let uu____15857 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          (uu____15857, q)
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____15848)))))
                                               in
                                            let uu____15886 =
                                              let uu____15917 =
                                                let uu____15946 =
                                                  let uu____15957 =
                                                    let uu____15966 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head1
                                                       in
                                                    (uu____15966,
                                                      FStar_Pervasives_Native.None,
                                                      chead2)
                                                     in
                                                  uu____15957 ::
                                                    arg_comps_rev
                                                   in
                                                FStar_List.map map_fun
                                                  uu____15946
                                                 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____15917
                                               in
                                            match uu____15886 with
                                            | (lifted_args,reverse_args) ->
                                                let uu____16167 =
                                                  let uu____16168 =
                                                    FStar_List.hd
                                                      reverse_args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____16168
                                                   in
                                                let uu____16189 =
                                                  let uu____16190 =
                                                    FStar_List.tl
                                                      reverse_args
                                                     in
                                                  FStar_List.rev uu____16190
                                                   in
                                                (lifted_args, uu____16167,
                                                  uu____16189)
                                             in
                                          match uu____15600 with
                                          | (lifted_args,head2,args1) ->
                                              let app =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  head2 args1 r
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
                                                uu___6_16299 =
                                                match uu___6_16299 with
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
                                                      let uu____16360 =
                                                        let uu____16361 =
                                                          let uu____16375 =
                                                            let uu____16378 =
                                                              let uu____16379
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____16379]
                                                               in
                                                            FStar_Syntax_Subst.close
                                                              uu____16378 e
                                                             in
                                                          ((false, [lb]),
                                                            uu____16375)
                                                           in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____16361
                                                         in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____16360
                                                        e.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (letbinding,
                                                           (FStar_Syntax_Syntax.Meta_monadic
                                                              (m,
                                                                (comp1.FStar_TypeChecker_Common.res_typ)))))
                                                      e.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_List.fold_left
                                                bind_lifted_args app2
                                                lifted_args)
                                        in
                                     let uu____16431 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1
                                        in
                                     (match uu____16431 with
                                      | (comp2,g) ->
                                          ((let uu____16449 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme
                                               in
                                            if uu____16449
                                            then
                                              let uu____16452 =
                                                FStar_Syntax_Print.term_to_string
                                                  app
                                                 in
                                              let uu____16454 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2
                                                 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____16452 uu____16454
                                            else ());
                                           (app, comp2, g)))))))
                  in
               let rec tc_args head_info uu____16543 bs args1 =
                 match uu____16543 with
                 | (subst,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____16706))::rest,
                         (uu____16708,FStar_Pervasives_Native.None )::uu____16709)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____16770 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head) env fvs t
                             in
                          (match uu____16770 with
                           | (t1,g_ex) ->
                               let r1 =
                                 match outargs with
                                 | [] -> head.FStar_Syntax_Syntax.pos
                                 | ((t2,uu____16801),uu____16802,uu____16803)::uu____16804
                                     ->
                                     let uu____16859 =
                                       FStar_Range.def_range
                                         head.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____16860 =
                                       let uu____16861 =
                                         FStar_Range.use_range
                                           head.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____16862 =
                                         FStar_Range.use_range
                                           t2.FStar_Syntax_Syntax.pos
                                          in
                                       FStar_Range.union_rng uu____16861
                                         uu____16862
                                        in
                                     FStar_Range.range_of_rng uu____16859
                                       uu____16860
                                  in
                               let uu____16863 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   r1 env t1
                                  in
                               (match uu____16863 with
                                | (varg,uu____16884,implicits) ->
                                    let subst1 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst  in
                                    let arg =
                                      let uu____16912 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____16912)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____16921 =
                                      let uu____16964 =
                                        let uu____16983 =
                                          let uu____17000 =
                                            let uu____17001 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____17001
                                              FStar_TypeChecker_Common.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____17000)
                                           in
                                        uu____16983 :: outargs  in
                                      (subst1, uu____16964, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____16921 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau_or_attr))::rest,
                         (uu____17071,FStar_Pervasives_Native.None )::uu____17072)
                          ->
                          let uu____17131 =
                            match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let tau1 = FStar_Syntax_Subst.subst subst tau
                                   in
                                let uu____17144 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau1
                                   in
                                (match uu____17144 with
                                 | (tau2,uu____17156,g_tau) ->
                                     let uu____17158 =
                                       let uu____17159 =
                                         let uu____17166 =
                                           FStar_Dyn.mkdyn env  in
                                         (uu____17166, tau2)  in
                                       FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                         uu____17159
                                        in
                                     (uu____17158, g_tau))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let attr1 =
                                  FStar_Syntax_Subst.subst subst attr  in
                                let uu____17173 =
                                  tc_tot_or_gtot_term env attr1  in
                                (match uu____17173 with
                                 | (attr2,uu____17185,g_attr) ->
                                     ((FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                         attr2), g_attr))
                             in
                          (match uu____17131 with
                           | (ctx_uvar_meta,g_tau_or_attr) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____17196 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head) env
                                   fvs t
                                  in
                               (match uu____17196 with
                                | (t1,g_ex) ->
                                    let r1 =
                                      match outargs with
                                      | [] -> head.FStar_Syntax_Syntax.pos
                                      | ((t2,uu____17227),uu____17228,uu____17229)::uu____17230
                                          ->
                                          let uu____17285 =
                                            FStar_Range.def_range
                                              head.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____17286 =
                                            let uu____17287 =
                                              FStar_Range.use_range
                                                head.FStar_Syntax_Syntax.pos
                                               in
                                            let uu____17288 =
                                              FStar_Range.use_range
                                                t2.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Range.union_rng uu____17287
                                              uu____17288
                                             in
                                          FStar_Range.range_of_rng
                                            uu____17285 uu____17286
                                       in
                                    let uu____17289 =
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        r1 env t1 FStar_Syntax_Syntax.Strict
                                        (FStar_Pervasives_Native.Some
                                           ctx_uvar_meta)
                                       in
                                    (match uu____17289 with
                                     | (varg,uu____17310,implicits) ->
                                         let subst1 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst  in
                                         let arg =
                                           let uu____17338 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____17338)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau_or_attr]
                                             implicits
                                            in
                                         let uu____17347 =
                                           let uu____17390 =
                                             let uu____17409 =
                                               let uu____17426 =
                                                 let uu____17427 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____17427
                                                   FStar_TypeChecker_Common.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____17426)
                                                in
                                             uu____17409 :: outargs  in
                                           (subst1, uu____17390, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____17347 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____17567,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____17568)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____17577),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____17578)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____17584),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____17585)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____17600 ->
                                let uu____17609 =
                                  let uu____17615 =
                                    let uu____17617 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____17619 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____17621 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____17623 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____17617 uu____17619 uu____17621
                                      uu____17623
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____17615)
                                   in
                                FStar_Errors.raise_error uu____17609
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst aqual  in
                            let x1 =
                              let uu___2366_17630 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2366_17630.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2366_17630.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____17632 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____17632
                             then
                               let uu____17635 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____17637 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____17639 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17641 =
                                 FStar_Syntax_Print.subst_to_string subst  in
                               let uu____17643 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____17635 uu____17637 uu____17639
                                 uu____17641 uu____17643
                             else ());
                            (let uu____17648 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head) env fvs
                                 targ
                                in
                             match uu____17648 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2375_17663 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2375_17663.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2375_17663.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2375_17663.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2375_17663.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2375_17663.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2375_17663.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2375_17663.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2375_17663.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2375_17663.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2375_17663.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2375_17663.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2375_17663.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2375_17663.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2375_17663.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2375_17663.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2375_17663.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___2375_17663.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2375_17663.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2375_17663.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2375_17663.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2375_17663.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2375_17663.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2375_17663.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2375_17663.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2375_17663.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2375_17663.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2375_17663.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2375_17663.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2375_17663.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2375_17663.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2375_17663.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2375_17663.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2375_17663.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2375_17663.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2375_17663.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2375_17663.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2375_17663.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2375_17663.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2375_17663.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2375_17663.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2375_17663.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2375_17663.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2375_17663.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2375_17663.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2375_17663.FStar_TypeChecker_Env.erasable_types_tab);
                                     FStar_TypeChecker_Env.enable_defer_to_tac
                                       =
                                       (uu___2375_17663.FStar_TypeChecker_Env.enable_defer_to_tac)
                                   }  in
                                 ((let uu____17665 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____17665
                                   then
                                     let uu____17668 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____17670 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____17672 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     let uu____17674 =
                                       FStar_Util.string_of_bool
                                         env2.FStar_TypeChecker_Env.use_eq
                                        in
                                     FStar_Util.print4
                                       "Checking arg (%s) %s at type %s with use_eq:%s\n"
                                       uu____17668 uu____17670 uu____17672
                                       uu____17674
                                   else ());
                                  (let uu____17679 = tc_term env2 e  in
                                   match uu____17679 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____17696 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____17696
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____17719 =
                                           let uu____17722 =
                                             let uu____17731 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____17731
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____17722
                                            in
                                         (uu____17719, aq)  in
                                       let uu____17740 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name)
                                          in
                                       if uu____17740
                                       then
                                         let subst1 =
                                           let uu____17750 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst
                                             uu____17750 e1
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
                      | (uu____17897,[]) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____17933) ->
                          let uu____17984 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs []
                             in
                          (match uu____17984 with
                           | (head1,chead1,ghead1) ->
                               let uu____18006 =
                                 let uu____18011 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1
                                    in
                                 FStar_All.pipe_right uu____18011
                                   (fun uu____18028  ->
                                      match uu____18028 with
                                      | (c,g1) ->
                                          let uu____18039 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1
                                             in
                                          (c, uu____18039))
                                  in
                               (match uu____18006 with
                                | (chead2,ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____18082 =
                                          FStar_Syntax_Subst.compress tres
                                           in
                                        FStar_All.pipe_right uu____18082
                                          FStar_Syntax_Util.unrefine
                                         in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1,cres') ->
                                          let uu____18113 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres'
                                             in
                                          (match uu____18113 with
                                           | (bs2,cres'1) ->
                                               let head_info1 =
                                                 (head1, chead2, ghead3,
                                                   cres'1)
                                                  in
                                               ((let uu____18136 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low
                                                    in
                                                 if uu____18136
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
                                      | uu____18199 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____18207 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env)
                                                 in
                                              FStar_All.pipe_right
                                                uu____18207
                                                FStar_Syntax_Util.unascribe
                                               in
                                            let uu____18208 =
                                              let uu____18209 =
                                                FStar_Syntax_Subst.compress
                                                  tres3
                                                 in
                                              uu____18209.FStar_Syntax_Syntax.n
                                               in
                                            match uu____18208 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____18212;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____18213;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},uu____18215)
                                                -> norm_tres tres4
                                            | uu____18223 -> tres3  in
                                          let uu____18224 = norm_tres tres1
                                             in
                                          aux true solve ghead3 uu____18224
                                      | uu____18226 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3
                                             in
                                          aux norm1 true ghead4 tres1
                                      | uu____18229 ->
                                          let uu____18230 =
                                            let uu____18236 =
                                              let uu____18238 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead
                                                 in
                                              let uu____18240 =
                                                FStar_Util.string_of_int
                                                  n_args
                                                 in
                                              let uu____18242 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1
                                                 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____18238 uu____18240
                                                uu____18242
                                               in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____18236)
                                             in
                                          let uu____18246 =
                                            FStar_Syntax_Syntax.argpos arg
                                             in
                                          FStar_Errors.raise_error
                                            uu____18230 uu____18246
                                       in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2))))
                  in
               let rec check_function_app tf guard =
                 let uu____18276 =
                   let uu____18277 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____18277.FStar_Syntax_Syntax.n  in
                 match uu____18276 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____18286 ->
                     let uu____18299 =
                       FStar_List.fold_right
                         (fun uu____18330  ->
                            fun uu____18331  ->
                              match uu____18331 with
                              | (bs,guard1) ->
                                  let uu____18358 =
                                    let uu____18371 =
                                      let uu____18372 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____18372
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____18371
                                     in
                                  (match uu____18358 with
                                   | (t,uu____18389,g) ->
                                       let uu____18403 =
                                         let uu____18406 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____18406 :: bs  in
                                       let uu____18407 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____18403, uu____18407))) args
                         ([], guard)
                        in
                     (match uu____18299 with
                      | (bs,guard1) ->
                          let uu____18424 =
                            let uu____18431 =
                              let uu____18444 =
                                let uu____18445 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____18445
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____18444
                               in
                            match uu____18431 with
                            | (t,uu____18462,g) ->
                                let uu____18476 = FStar_Options.ml_ish ()  in
                                if uu____18476
                                then
                                  let uu____18485 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____18488 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____18485, uu____18488)
                                else
                                  (let uu____18493 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____18496 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____18493, uu____18496))
                             in
                          (match uu____18424 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____18515 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____18515
                                 then
                                   let uu____18519 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let uu____18521 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____18523 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____18519 uu____18521 uu____18523
                                 else ());
                                (let g =
                                   let uu____18529 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____18529
                                    in
                                 let uu____18530 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____18530))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____18531;
                        FStar_Syntax_Syntax.pos = uu____18532;
                        FStar_Syntax_Syntax.vars = uu____18533;_},uu____18534)
                     ->
                     let uu____18571 =
                       FStar_List.fold_right
                         (fun uu____18602  ->
                            fun uu____18603  ->
                              match uu____18603 with
                              | (bs,guard1) ->
                                  let uu____18630 =
                                    let uu____18643 =
                                      let uu____18644 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____18644
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____18643
                                     in
                                  (match uu____18630 with
                                   | (t,uu____18661,g) ->
                                       let uu____18675 =
                                         let uu____18678 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____18678 :: bs  in
                                       let uu____18679 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____18675, uu____18679))) args
                         ([], guard)
                        in
                     (match uu____18571 with
                      | (bs,guard1) ->
                          let uu____18696 =
                            let uu____18703 =
                              let uu____18716 =
                                let uu____18717 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____18717
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____18716
                               in
                            match uu____18703 with
                            | (t,uu____18734,g) ->
                                let uu____18748 = FStar_Options.ml_ish ()  in
                                if uu____18748
                                then
                                  let uu____18757 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____18760 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____18757, uu____18760)
                                else
                                  (let uu____18765 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____18768 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____18765, uu____18768))
                             in
                          (match uu____18696 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____18787 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____18787
                                 then
                                   let uu____18791 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let uu____18793 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____18795 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____18791 uu____18793 uu____18795
                                 else ());
                                (let g =
                                   let uu____18801 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____18801
                                    in
                                 let uu____18802 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____18802))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____18825 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____18825 with
                      | (bs1,c1) ->
                          let head_info = (head, chead, ghead, c1)  in
                          ((let uu____18848 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____18848
                            then
                              let uu____18851 =
                                FStar_Syntax_Print.term_to_string head  in
                              let uu____18853 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____18855 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____18858 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____18851 uu____18853 uu____18855
                                uu____18858
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____18920) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____18926,uu____18927) ->
                     check_function_app t guard
                 | uu____18968 ->
                     let uu____18969 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____18969
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
                  let uu____19052 =
                    FStar_List.fold_left2
                      (fun uu____19121  ->
                         fun uu____19122  ->
                           fun uu____19123  ->
                             match (uu____19121, uu____19122, uu____19123)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____19276 =
                                     let uu____19278 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____19278 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____19276
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____19284 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                       "arguments to short circuiting operators must be pure or ghost"
                                      in
                                   match uu____19284 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen
                                          in
                                       let g1 =
                                         let uu____19314 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____19314 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____19319 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____19319)
                                              &&
                                              (let uu____19322 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name
                                                  in
                                               Prims.op_Negation uu____19322))
                                          in
                                       let uu____19324 =
                                         let uu____19335 =
                                           let uu____19346 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____19346]  in
                                         FStar_List.append seen uu____19335
                                          in
                                       let uu____19379 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____19324, uu____19379, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____19052 with
                   | (args1,guard,ghost) ->
                       let e = FStar_Syntax_Syntax.mk_Tm_app head args1 r  in
                       let c1 =
                         if ghost
                         then
                           let uu____19445 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____19445
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c  in
                       let uu____19448 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____19448 with | (c2,g) -> (e, c2, g)))
              | uu____19465 ->
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
            let uu____19563 = FStar_Syntax_Util.head_and_args t1  in
            match uu____19563 with
            | (head,args) ->
                let uu____19606 =
                  let uu____19607 = FStar_Syntax_Subst.compress head  in
                  uu____19607.FStar_Syntax_Syntax.n  in
                (match uu____19606 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____19611;
                        FStar_Syntax_Syntax.vars = uu____19612;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____19619 ->
                     if norm1
                     then t1
                     else
                       (let uu____19623 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____19623))
          
          and unfold_once t f us args =
            let uu____19641 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____19641
            then t
            else
              (let uu____19646 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____19646 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____19666 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____19666 with
                    | (uu____19671,head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            t.FStar_Syntax_Syntax.pos
                           in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t'
                           in
                        aux false t'1))
           in
          let uu____19676 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____19676  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____19695 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19695
           then
             let uu____19700 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____19702 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____19700 uu____19702
           else ());
          (let fail1 msg =
             let msg1 =
               let uu____19722 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____19724 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____19722 uu____19724 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____19728 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____19728 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____19772 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____19772 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____19773;
                    FStar_Syntax_Syntax.pos = uu____19774;
                    FStar_Syntax_Syntax.vars = uu____19775;_} ->
                    let uu____19778 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____19778 with
                     | (head_p,args_p) ->
                         let uu____19821 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____19821
                         then
                           let uu____19824 =
                             let uu____19825 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____19825.FStar_Syntax_Syntax.n  in
                           (match uu____19824 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____19830 =
                                    let uu____19832 =
                                      let uu____19834 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____19834
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____19832
                                     in
                                  if uu____19830
                                  then
                                    fail1
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail1 ""
                                 else ();
                                 (let uu____19862 =
                                    let uu____19887 =
                                      let uu____19891 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____19891
                                       in
                                    match uu____19887 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n ->
                                        let uu____19940 =
                                          FStar_Util.first_N n args_p  in
                                        (match uu____19940 with
                                         | (params_p,uu____19998) ->
                                             let uu____20039 =
                                               FStar_Util.first_N n args_s
                                                in
                                             (match uu____20039 with
                                              | (params_s,uu____20097) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____19862 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____20226  ->
                                             fun uu____20227  ->
                                               match (uu____20226,
                                                       uu____20227)
                                               with
                                               | ((p,uu____20261),(s,uu____20263))
                                                   ->
                                                   let uu____20296 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____20296 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____20299 =
                                                          let uu____20301 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____20303 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____20301
                                                            uu____20303
                                                           in
                                                        fail1 uu____20299
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
                            | uu____20308 ->
                                fail1 "Pattern matching a non-inductive type")
                         else
                           (let uu____20312 =
                              let uu____20314 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____20316 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____20314 uu____20316
                               in
                            fail1 uu____20312))
                | uu____20319 ->
                    let uu____20320 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____20320 with
                     | FStar_Pervasives_Native.None  -> fail1 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____20363 = FStar_Syntax_Util.head_and_args e  in
          match uu____20363 with
          | (head,args) ->
              (match head.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____20433 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____20433 with
                    | (us,t_f) ->
                        let uu____20453 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____20453 with
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
                              (let rec aux uu____20564 formals1 args1 =
                                 match uu____20564 with
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
                                              e.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____20709 =
                                            FStar_Syntax_Subst.subst subst t
                                             in
                                          (pat_e, uu____20709, bvs, guard,
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
                                                  let uu___2682_20819 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2682_20819.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2682_20819.FStar_Syntax_Syntax.index);
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
                                               let uu____20971 =
                                                 let uu____20994 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst1,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____20994)
                                                  in
                                               aux uu____20971 formals2 args2)
                                      | uu____21033 ->
                                          fail "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____21090 -> fail "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____21156 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____21156
           then
             let uu____21161 = FStar_Syntax_Print.pat_to_string p  in
             let uu____21163 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____21161
               uu____21163
           else ());
          (let id =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None
              in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____21188 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t
                  in
               FStar_All.pipe_right uu____21188 FStar_Syntax_Syntax.mk_binder
                in
             let tm =
               let uu____21197 =
                 let uu____21198 =
                   let uu____21207 =
                     let uu____21208 =
                       FStar_All.pipe_right x_b FStar_Pervasives_Native.fst
                        in
                     FStar_All.pipe_right uu____21208
                       FStar_Syntax_Syntax.bv_to_name
                      in
                   FStar_All.pipe_right uu____21207
                     FStar_Syntax_Syntax.as_arg
                    in
                 [uu____21198]  in
               FStar_Syntax_Syntax.mk_Tm_app disc uu____21197
                 FStar_Range.dummyRange
                in
             let tm1 =
               let uu____21242 =
                 let uu____21243 =
                   FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg  in
                 [uu____21243]  in
               FStar_Syntax_Syntax.mk_Tm_app inner_t uu____21242
                 FStar_Range.dummyRange
                in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None  in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____21305 ->
               let uu____21312 =
                 let uu____21314 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____21314
                  in
               failwith uu____21312
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2721_21336 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2721_21336.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2721_21336.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____21337 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id], uu____21337,
                 (let uu___2724_21344 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2724_21344.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2728_21348 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2728_21348.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2728_21348.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____21349 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id], uu____21349,
                 (let uu___2731_21356 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2731_21356.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant uu____21358 ->
               let uu____21359 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____21359 with
                | (uu____21388,e_c,uu____21390,uu____21391) ->
                    let uu____21396 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____21396 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____21426 =
                              let uu____21428 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t
                                 in
                              Prims.op_Negation uu____21428  in
                            if uu____21426
                            then
                              let uu____21431 =
                                let uu____21433 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ
                                   in
                                let uu____21435 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____21433 uu____21435
                                 in
                              fail uu____21431
                            else ());
                           ([], [], e_c1, p,
                             FStar_TypeChecker_Env.trivial_guard, false)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____21497  ->
                        match uu____21497 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____21527
                                 -> (p1, b)
                             | uu____21537 ->
                                 let uu____21538 =
                                   let uu____21541 =
                                     let uu____21542 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____21542
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____21541
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____21538, b))) sub_pats
                    in
                 let uu___2759_21546 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2759_21546.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____21591  ->
                         match uu____21591 with
                         | (x,uu____21601) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____21609
                                  -> false
                              | uu____21617 -> true)))
                  in
               let uu____21619 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____21619 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____21663 =
                          let uu____21665 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____21667 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____21669 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____21676 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____21665 uu____21667 uu____21669 uu____21676
                           in
                        failwith uu____21663)
                     else ();
                     (let uu____21681 =
                        let uu____21693 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____21693 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard,erasable)
                            ->
                            let g' =
                              let uu____21730 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____21730  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____21733 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____21733
                              then
                                let uu____21738 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____21740 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____21742 =
                                  let uu____21744 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____21752 =
                                           let uu____21754 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____21756 =
                                             let uu____21758 =
                                               let uu____21760 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____21760 ")"
                                                in
                                             Prims.op_Hat " : " uu____21758
                                              in
                                           Prims.op_Hat uu____21754
                                             uu____21756
                                            in
                                         Prims.op_Hat "(" uu____21752)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____21744
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____21738 uu____21740 uu____21742
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable))
                         in
                      match uu____21681 with
                      | (simple_pat_e1,simple_bvs1,g1,erasable) ->
                          let uu____21803 =
                            let uu____21835 =
                              let uu____21867 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], [], uu____21867, erasable,
                                Prims.int_zero)
                               in
                            FStar_List.fold_left2
                              (fun uu____21949  ->
                                 fun uu____21950  ->
                                   fun x  ->
                                     match (uu____21949, uu____21950) with
                                     | ((env2,bvs,tms,pats,subst,g,erasable1,i),
                                        (p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____22134 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____22134 with
                                          | (bvs_p,tms_p,e_p,p2,g',erasable_p)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____22204 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____22204 i
                                                   in
                                                let uu____22205 =
                                                  let uu____22214 =
                                                    let uu____22219 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    mk_disc_t uu____22219  in
                                                  FStar_List.map uu____22214
                                                   in
                                                FStar_All.pipe_right tms_p
                                                  uu____22205
                                                 in
                                              let uu____22225 =
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
                                                uu____22225,
                                                (erasable1 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____21835 sub_pats1 simple_bvs1
                             in
                          (match uu____21803 with
                           | (_env,bvs,tms,checked_sub_pats,subst,g,erasable1,uu____22284)
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
                                              let uu___2843_22460 = hd  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2843_22460.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____22465 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd1, b) :: uu____22465
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd1,uu____22509)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____22546 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd1, b) :: uu____22546
                                             | uu____22566 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____22592 ->
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
                                     let uu___2864_22635 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2864_22635.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____22647 -> failwith "Impossible"  in
                               let uu____22651 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, tms, pat_e, uu____22651, g, erasable1))))))
           in
        (let uu____22658 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____22658
         then
           let uu____22663 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____22663
         else ());
        (let uu____22668 =
           let uu____22686 =
             let uu___2869_22687 =
               let uu____22688 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____22688 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2869_22687.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2869_22687.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2869_22687.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2869_22687.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2869_22687.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2869_22687.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2869_22687.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2869_22687.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2869_22687.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2869_22687.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2869_22687.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2869_22687.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2869_22687.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2869_22687.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2869_22687.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2869_22687.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___2869_22687.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2869_22687.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2869_22687.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2869_22687.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2869_22687.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2869_22687.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2869_22687.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2869_22687.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2869_22687.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2869_22687.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2869_22687.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2869_22687.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2869_22687.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2869_22687.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2869_22687.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2869_22687.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2869_22687.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2869_22687.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2869_22687.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2869_22687.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2869_22687.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2869_22687.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2869_22687.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2869_22687.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2869_22687.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2869_22687.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2869_22687.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2869_22687.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2869_22687.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___2869_22687.FStar_TypeChecker_Env.enable_defer_to_tac)
             }  in
           let uu____22704 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____22686 uu____22704 pat_t  in
         match uu____22668 with
         | (bvs,tms,pat_e,pat,g,erasable) ->
             ((let uu____22743 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____22743
               then
                 let uu____22748 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____22750 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____22748
                   uu____22750
               else ());
              (let uu____22755 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____22756 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, tms, uu____22755, pat_e, uu____22756, g, erasable))))

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
        let uu____22794 = FStar_Syntax_Subst.open_branch branch  in
        match uu____22794 with
        | (pattern,when_clause,branch_exp) ->
            let uu____22843 = branch  in
            (match uu____22843 with
             | (cpat,uu____22874,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____22896 =
                   let uu____22903 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____22903
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____22896 with
                  | (scrutinee_env,uu____22940) ->
                      let uu____22945 = tc_pat env pat_t pattern  in
                      (match uu____22945 with
                       | (pattern1,pat_bvs,pat_bv_tms,pat_env,pat_exp,norm_pat_exp,guard_pat,erasable)
                           ->
                           ((let uu____23015 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____23015
                             then
                               let uu____23019 =
                                 FStar_Syntax_Print.pat_to_string pattern1
                                  in
                               let uu____23021 =
                                 FStar_Syntax_Print.bvs_to_string ";" pat_bvs
                                  in
                               let uu____23024 =
                                 FStar_List.fold_left
                                   (fun s  ->
                                      fun t  ->
                                        let uu____23033 =
                                          let uu____23035 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat ";" uu____23035  in
                                        Prims.op_Hat s uu____23033) ""
                                   pat_bv_tms
                                  in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____23019 uu____23021 uu____23024
                             else ());
                            (let uu____23042 =
                               match when_clause with
                               | FStar_Pervasives_Native.None  ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____23072 =
                                     FStar_TypeChecker_Env.should_verify env
                                      in
                                   if uu____23072
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____23095 =
                                        let uu____23102 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool
                                           in
                                        tc_term uu____23102 e  in
                                      match uu____23095 with
                                      | (e1,c,g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g))
                                in
                             match uu____23042 with
                             | (when_clause1,g_when) ->
                                 let uu____23159 = tc_term pat_env branch_exp
                                    in
                                 (match uu____23159 with
                                  | (branch_exp1,c,g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None  ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____23218 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool
                                                 in
                                              FStar_All.pipe_left
                                                (fun uu____23229  ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____23229) uu____23218
                                           in
                                        let branch_guard =
                                          let uu____23233 =
                                            let uu____23235 =
                                              FStar_TypeChecker_Env.should_verify
                                                env
                                               in
                                            Prims.op_Negation uu____23235  in
                                          if uu____23233
                                          then FStar_Syntax_Util.t_true
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____23291 =
                                                   let uu____23299 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v
                                                      in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____23299
                                                    in
                                                 match uu____23291 with
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
                                                       let uu____23315 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator
                                                          in
                                                       (match uu____23315
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                             -> []
                                                        | uu____23336 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let disc1 =
                                                              let uu____23350
                                                                =
                                                                let uu____23351
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                   in
                                                                [uu____23351]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____23350
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____23376 =
                                                              FStar_Syntax_Util.mk_eq2
                                                                FStar_Syntax_Syntax.U_zero
                                                                FStar_Syntax_Util.t_bool
                                                                disc1
                                                                FStar_Syntax_Util.exp_true_bool
                                                               in
                                                            [uu____23376])
                                                     else []
                                                  in
                                               let fail uu____23384 =
                                                 let uu____23385 =
                                                   let uu____23387 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos
                                                      in
                                                   let uu____23389 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1
                                                      in
                                                   let uu____23391 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1
                                                      in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____23387 uu____23389
                                                     uu____23391
                                                    in
                                                 failwith uu____23385  in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1,uu____23406) ->
                                                     head_constructor t1
                                                 | uu____23411 -> fail ()  in
                                               let force_scrutinee
                                                 uu____23417 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____23418 =
                                                       let uu____23420 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p
                                                          in
                                                       let uu____23422 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2
                                                          in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____23420
                                                         uu____23422
                                                        in
                                                     failwith uu____23418
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t
                                                  in
                                               let pat_exp2 =
                                                 let uu____23429 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____23429
                                                   FStar_Syntax_Util.unmeta
                                                  in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____23434,FStar_Syntax_Syntax.Tm_name
                                                  uu____23435) -> []
                                               | (uu____23436,FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit ))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____23439 =
                                                     let uu____23440 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1
                                                        in
                                                     let uu____23441 =
                                                       force_scrutinee ()  in
                                                     FStar_Syntax_Util.mk_eq2
                                                       FStar_Syntax_Syntax.U_zero
                                                       uu____23440
                                                       uu____23441 pat_exp2
                                                      in
                                                   [uu____23439]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____23442,FStar_Pervasives_Native.Some
                                                   uu____23443)),uu____23444)
                                                   ->
                                                   let uu____23461 =
                                                     let uu____23468 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env
                                                        in
                                                     match uu____23468 with
                                                     | (env1,uu____23482) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2
                                                      in
                                                   (match uu____23461 with
                                                    | (uu____23489,t,uu____23491)
                                                        ->
                                                        let uu____23492 =
                                                          let uu____23493 =
                                                            force_scrutinee
                                                              ()
                                                             in
                                                          FStar_Syntax_Util.mk_eq2
                                                            FStar_Syntax_Syntax.U_zero
                                                            t uu____23493
                                                            pat_exp2
                                                           in
                                                        [uu____23492])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____23494,[]),FStar_Syntax_Syntax.Tm_uinst
                                                  uu____23495) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____23519 =
                                                     let uu____23521 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____23521
                                                      in
                                                   if uu____23519
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____23531 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____23534 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____23531
                                                        uu____23534)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____23537,[]),FStar_Syntax_Syntax.Tm_fvar
                                                  uu____23538) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____23556 =
                                                     let uu____23558 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____23558
                                                      in
                                                   if uu____23556
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____23568 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____23571 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____23568
                                                        uu____23571)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____23574,pat_args),FStar_Syntax_Syntax.Tm_app
                                                  (head,args)) ->
                                                   let f =
                                                     head_constructor head
                                                      in
                                                   let uu____23621 =
                                                     (let uu____23625 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      Prims.op_Negation
                                                        uu____23625)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args))
                                                      in
                                                   if uu____23621
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____23653 =
                                                          let uu____23658 =
                                                            FStar_List.zip
                                                              pat_args args
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____23658
                                                            (FStar_List.mapi
                                                               (fun i  ->
                                                                  fun
                                                                    uu____23744
                                                                     ->
                                                                    match uu____23744
                                                                    with
                                                                    | 
                                                                    ((pi,uu____23766),
                                                                    (ei,uu____23768))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____23796
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____23796
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____23817
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____23829
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____23829
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____23831
                                                                    =
                                                                    let uu____23832
                                                                    =
                                                                    let uu____23833
                                                                    =
                                                                    let uu____23842
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____23842
                                                                     in
                                                                    [uu____23833]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____23832
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____23831
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____23653
                                                          FStar_List.flatten
                                                         in
                                                      let uu____23865 =
                                                        let uu____23868 =
                                                          force_scrutinee ()
                                                           in
                                                        discriminate
                                                          uu____23868 f
                                                         in
                                                      FStar_List.append
                                                        uu____23865
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____23871,uu____23872) ->
                                                   []
                                               | uu____23879 ->
                                                   let uu____23884 =
                                                     let uu____23886 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2
                                                        in
                                                     let uu____23888 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2
                                                        in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____23886
                                                       uu____23888
                                                      in
                                                   failwith uu____23884
                                                in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____23917 =
                                                 let uu____23919 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____23919
                                                  in
                                               if uu____23917
                                               then
                                                 FStar_TypeChecker_Util.fvar_const
                                                   env
                                                   FStar_Parser_Const.true_lid
                                               else
                                                 (let t =
                                                    let uu____23925 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_conj_l
                                                      uu____23925
                                                     in
                                                  let uu____23934 =
                                                    FStar_Syntax_Util.type_u
                                                      ()
                                                     in
                                                  match uu____23934 with
                                                  | (k,uu____23940) ->
                                                      let uu____23941 =
                                                        tc_check_tot_or_gtot_term
                                                          scrutinee_env t k
                                                          ""
                                                         in
                                                      (match uu____23941 with
                                                       | (t1,uu____23950,uu____23951)
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
                                        let uu____23965 =
                                          let eqs =
                                            let uu____23985 =
                                              let uu____23987 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____23987
                                               in
                                            if uu____23985
                                            then FStar_Pervasives_Native.None
                                            else
                                              (let e =
                                                 FStar_Syntax_Subst.compress
                                                   pat_exp
                                                  in
                                               let uu____23995 =
                                                 let uu____23996 =
                                                   env.FStar_TypeChecker_Env.universe_of
                                                     env pat_t
                                                    in
                                                 FStar_Syntax_Util.mk_eq2
                                                   uu____23996 pat_t
                                                   scrutinee_tm e
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____23995)
                                             in
                                          let uu____23997 =
                                            FStar_TypeChecker_Util.strengthen_precondition
                                              FStar_Pervasives_Native.None
                                              env branch_exp1 c g_branch
                                             in
                                          match uu____23997 with
                                          | (c1,g_branch1) ->
                                              let branch_has_layered_effect =
                                                let uu____24026 =
                                                  FStar_All.pipe_right
                                                    c1.FStar_TypeChecker_Common.eff_name
                                                    (FStar_TypeChecker_Env.norm_eff_name
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____24026
                                                  (FStar_TypeChecker_Env.is_layered_effect
                                                     env)
                                                 in
                                              let uu____24028 =
                                                let env1 =
                                                  let uu____24034 =
                                                    FStar_All.pipe_right
                                                      pat_bvs
                                                      (FStar_List.map
                                                         FStar_Syntax_Syntax.mk_binder)
                                                     in
                                                  FStar_TypeChecker_Env.push_binders
                                                    scrutinee_env uu____24034
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
                                                   | uu____24055 when
                                                       let uu____24066 =
                                                         FStar_TypeChecker_Env.should_verify
                                                           env1
                                                          in
                                                       Prims.op_Negation
                                                         uu____24066
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
                                                       let uu____24087 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 gf
                                                          in
                                                       let uu____24088 =
                                                         FStar_TypeChecker_Env.imp_guard
                                                           g g_when
                                                          in
                                                       (uu____24087,
                                                         uu____24088)
                                                   | (FStar_Pervasives_Native.Some
                                                      f,FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_f =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           f
                                                          in
                                                       let g_fw =
                                                         let uu____24103 =
                                                           FStar_Syntax_Util.mk_conj
                                                             f w
                                                            in
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           uu____24103
                                                          in
                                                       let uu____24104 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_fw
                                                          in
                                                       let uu____24105 =
                                                         let uu____24106 =
                                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                                             g_f
                                                            in
                                                         FStar_TypeChecker_Env.imp_guard
                                                           uu____24106 g_when
                                                          in
                                                       (uu____24104,
                                                         uu____24105)
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
                                                       let uu____24120 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_w
                                                          in
                                                       (uu____24120, g_when))
                                                 in
                                              (match uu____24028 with
                                               | (c_weak,g_when_weak) ->
                                                   let binders =
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder
                                                       pat_bvs
                                                      in
                                                   let maybe_return_c_weak
                                                     should_return =
                                                     let c_weak1 =
                                                       let uu____24163 =
                                                         should_return &&
                                                           (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                              c_weak)
                                                          in
                                                       if uu____24163
                                                       then
                                                         FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                           env branch_exp1
                                                           c_weak
                                                       else c_weak  in
                                                     if
                                                       branch_has_layered_effect
                                                     then
                                                       ((let uu____24170 =
                                                           FStar_All.pipe_left
                                                             (FStar_TypeChecker_Env.debug
                                                                env)
                                                             (FStar_Options.Other
                                                                "LayeredEffects")
                                                            in
                                                         if uu____24170
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
                                                                   let uu____24188
                                                                    =
                                                                    let uu____24189
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____24189]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____24188
                                                                    FStar_Range.dummyRange))
                                                            in
                                                         let pat_bv_tms2 =
                                                           let env1 =
                                                             let uu___3102_24226
                                                               =
                                                               FStar_TypeChecker_Env.push_bv
                                                                 env
                                                                 scrutinee
                                                                in
                                                             {
                                                               FStar_TypeChecker_Env.solver
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.solver);
                                                               FStar_TypeChecker_Env.range
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.range);
                                                               FStar_TypeChecker_Env.curmodule
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.curmodule);
                                                               FStar_TypeChecker_Env.gamma
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.gamma);
                                                               FStar_TypeChecker_Env.gamma_sig
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.gamma_sig);
                                                               FStar_TypeChecker_Env.gamma_cache
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.gamma_cache);
                                                               FStar_TypeChecker_Env.modules
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.modules);
                                                               FStar_TypeChecker_Env.expected_typ
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.expected_typ);
                                                               FStar_TypeChecker_Env.sigtab
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.sigtab);
                                                               FStar_TypeChecker_Env.attrtab
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.attrtab);
                                                               FStar_TypeChecker_Env.instantiate_imp
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.instantiate_imp);
                                                               FStar_TypeChecker_Env.effects
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.effects);
                                                               FStar_TypeChecker_Env.generalize
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.generalize);
                                                               FStar_TypeChecker_Env.letrecs
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.letrecs);
                                                               FStar_TypeChecker_Env.top_level
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.top_level);
                                                               FStar_TypeChecker_Env.check_uvars
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.check_uvars);
                                                               FStar_TypeChecker_Env.use_eq
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.use_eq);
                                                               FStar_TypeChecker_Env.use_eq_strict
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.use_eq_strict);
                                                               FStar_TypeChecker_Env.is_iface
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.is_iface);
                                                               FStar_TypeChecker_Env.admit
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.admit);
                                                               FStar_TypeChecker_Env.lax
                                                                 = true;
                                                               FStar_TypeChecker_Env.lax_universes
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.lax_universes);
                                                               FStar_TypeChecker_Env.phase1
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.phase1);
                                                               FStar_TypeChecker_Env.failhard
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.failhard);
                                                               FStar_TypeChecker_Env.nosynth
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.nosynth);
                                                               FStar_TypeChecker_Env.uvar_subtyping
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.uvar_subtyping);
                                                               FStar_TypeChecker_Env.tc_term
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.tc_term);
                                                               FStar_TypeChecker_Env.type_of
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.type_of);
                                                               FStar_TypeChecker_Env.universe_of
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.universe_of);
                                                               FStar_TypeChecker_Env.check_type_of
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.check_type_of);
                                                               FStar_TypeChecker_Env.use_bv_sorts
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.use_bv_sorts);
                                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                               FStar_TypeChecker_Env.normalized_eff_names
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.normalized_eff_names);
                                                               FStar_TypeChecker_Env.fv_delta_depths
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.fv_delta_depths);
                                                               FStar_TypeChecker_Env.proof_ns
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.proof_ns);
                                                               FStar_TypeChecker_Env.synth_hook
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.synth_hook);
                                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                               FStar_TypeChecker_Env.splice
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.splice);
                                                               FStar_TypeChecker_Env.mpreprocess
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.mpreprocess);
                                                               FStar_TypeChecker_Env.postprocess
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.postprocess);
                                                               FStar_TypeChecker_Env.identifier_info
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.identifier_info);
                                                               FStar_TypeChecker_Env.tc_hooks
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.tc_hooks);
                                                               FStar_TypeChecker_Env.dsenv
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.dsenv);
                                                               FStar_TypeChecker_Env.nbe
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.nbe);
                                                               FStar_TypeChecker_Env.strict_args_tab
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.strict_args_tab);
                                                               FStar_TypeChecker_Env.erasable_types_tab
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.erasable_types_tab);
                                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                                 =
                                                                 (uu___3102_24226.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                             }  in
                                                           let uu____24228 =
                                                             let uu____24231
                                                               =
                                                               FStar_List.fold_left2
                                                                 (fun
                                                                    uu____24259
                                                                     ->
                                                                    fun
                                                                    pat_bv_tm
                                                                     ->
                                                                    fun bv 
                                                                    ->
                                                                    match uu____24259
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
                                                                    let uu____24300
                                                                    =
                                                                    let uu____24307
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pat_bv_tm
                                                                    (FStar_Syntax_Subst.subst
                                                                    substs)
                                                                     in
                                                                    let uu____24308
                                                                    =
                                                                    let uu____24319
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t
                                                                     in
                                                                    tc_trivial_guard
                                                                    uu____24319
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24307
                                                                    uu____24308
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24300
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
                                                               uu____24231
                                                               FStar_Pervasives_Native.snd
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____24228
                                                             (FStar_List.map
                                                                (FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Env.Beta]
                                                                   env1))
                                                            in
                                                         (let uu____24381 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects")
                                                             in
                                                          if uu____24381
                                                          then
                                                            let uu____24386 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____24395
                                                                    =
                                                                    let uu____24397
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____24397
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____24395)
                                                                ""
                                                                pat_bv_tms2
                                                               in
                                                            let uu____24401 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____24410
                                                                    =
                                                                    let uu____24412
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____24412
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____24410)
                                                                "" pat_bvs
                                                               in
                                                            FStar_Util.print2
                                                              "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                                                              uu____24386
                                                              uu____24401
                                                          else ());
                                                         (let uu____24419 =
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
                                                          let uu____24426 =
                                                            let uu____24431 =
                                                              FStar_TypeChecker_Env.push_bv
                                                                env scrutinee
                                                               in
                                                            FStar_TypeChecker_Util.close_layered_lcomp
                                                              uu____24431
                                                              pat_bvs
                                                              pat_bv_tms2
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____24419
                                                            uu____24426)))
                                                     else
                                                       FStar_TypeChecker_Util.close_wp_lcomp
                                                         env pat_bvs c_weak1
                                                      in
                                                   let uu____24434 =
                                                     FStar_TypeChecker_Env.close_guard
                                                       env binders
                                                       g_when_weak
                                                      in
                                                   let uu____24435 =
                                                     FStar_TypeChecker_Env.conj_guard
                                                       guard_pat g_branch1
                                                      in
                                                   ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                     (c_weak.FStar_TypeChecker_Common.cflags),
                                                     maybe_return_c_weak,
                                                     uu____24434,
                                                     uu____24435))
                                           in
                                        match uu____23965 with
                                        | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                            ->
                                            let guard =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_when1 g_branch1
                                               in
                                            ((let uu____24490 =
                                                FStar_TypeChecker_Env.debug
                                                  env FStar_Options.High
                                                 in
                                              if uu____24490
                                              then
                                                let uu____24493 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____24493
                                              else ());
                                             (let uu____24499 =
                                                FStar_Syntax_Subst.close_branch
                                                  (pattern1, when_clause1,
                                                    branch_exp1)
                                                 in
                                              let uu____24516 =
                                                let uu____24517 =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs
                                                   in
                                                FStar_TypeChecker_Util.close_guard_implicits
                                                  env false uu____24517 guard
                                                 in
                                              (uu____24499, branch_guard,
                                                effect_label, cflags,
                                                maybe_return_c, uu____24516,
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
          let uu____24566 = check_let_bound_def true env1 lb  in
          (match uu____24566 with
           | (e1,univ_vars,c1,g1,annotated) ->
               let uu____24592 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24614 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____24614, univ_vars, c1)
                 else
                   (let g11 =
                      let uu____24620 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____24620
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____24621 = FStar_TypeChecker_Common.lcomp_comp c1
                       in
                    match uu____24621 with
                    | (comp1,g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1  in
                        let uu____24639 =
                          let uu____24652 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)]
                             in
                          FStar_List.hd uu____24652  in
                        (match uu____24639 with
                         | (uu____24702,univs,e11,c11,gvs) ->
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
                             let uu____24716 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11  in
                             (g14, e11, univs, uu____24716)))
                  in
               (match uu____24592 with
                | (g11,e11,univ_vars1,c11) ->
                    let uu____24733 =
                      let uu____24742 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____24742
                      then
                        let uu____24753 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____24753 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____24787 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____24787
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____24788 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____24788, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____24800 =
                            FStar_TypeChecker_Common.lcomp_comp c11  in
                          match uu____24800 with
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
                                  let uu____24824 =
                                    FStar_Syntax_Util.is_pure_comp c  in
                                  if uu____24824
                                  then e2
                                  else
                                    ((let uu____24832 =
                                        FStar_TypeChecker_Env.get_range env1
                                         in
                                      FStar_Errors.log_issue uu____24832
                                        FStar_TypeChecker_Err.top_level_effect);
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Masked_effect)))
                                       e2.FStar_Syntax_Syntax.pos)
                                   in
                                (e21, c)))))
                       in
                    (match uu____24733 with
                     | (e21,c12) ->
                         ((let uu____24856 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____24856
                           then
                             let uu____24859 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____24859
                           else ());
                          (let e12 =
                             let uu____24865 = FStar_Options.tcnorm ()  in
                             if uu____24865
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
                           (let uu____24871 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____24871
                            then
                              let uu____24874 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____24874
                            else ());
                           (let cres =
                              let uu____24880 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12
                                 in
                              if uu____24880
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
                                   | (wp,uu____24888)::[] -> wp
                                   | uu____24913 ->
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
                                   let uu____24928 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [FStar_Syntax_Syntax.U_zero] env1
                                       c1_eff_decl ret
                                      in
                                   let uu____24929 =
                                     let uu____24930 =
                                       FStar_Syntax_Syntax.as_arg
                                         FStar_Syntax_Syntax.t_unit
                                        in
                                     let uu____24939 =
                                       let uu____24950 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.unit_const
                                          in
                                       [uu____24950]  in
                                     uu____24930 :: uu____24939  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____24928
                                     uu____24929 e21.FStar_Syntax_Syntax.pos
                                    in
                                 let wp =
                                   let bind =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator
                                      in
                                   let uu____24985 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       (FStar_List.append
                                          c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                          [FStar_Syntax_Syntax.U_zero]) env1
                                       c1_eff_decl bind
                                      in
                                   let uu____24986 =
                                     let uu____24987 =
                                       let uu____24996 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_constant
                                              (FStar_Const.Const_range
                                                 (lb.FStar_Syntax_Syntax.lbpos)))
                                           lb.FStar_Syntax_Syntax.lbpos
                                          in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____24996
                                        in
                                     let uu____25005 =
                                       let uu____25016 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                          in
                                       let uu____25033 =
                                         let uu____25044 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.t_unit
                                            in
                                         let uu____25053 =
                                           let uu____25064 =
                                             FStar_Syntax_Syntax.as_arg c1_wp
                                              in
                                           let uu____25073 =
                                             let uu____25084 =
                                               let uu____25093 =
                                                 let uu____25094 =
                                                   let uu____25095 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                                      in
                                                   [uu____25095]  in
                                                 FStar_Syntax_Util.abs
                                                   uu____25094 wp2
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Util.mk_residual_comp
                                                         FStar_Parser_Const.effect_Tot_lid
                                                         FStar_Pervasives_Native.None
                                                         [FStar_Syntax_Syntax.TOTAL]))
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____25093
                                                in
                                             [uu____25084]  in
                                           uu____25064 :: uu____25073  in
                                         uu____25044 :: uu____25053  in
                                       uu____25016 :: uu____25033  in
                                     uu____24987 :: uu____25005  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____24985
                                     uu____24986 lb.FStar_Syntax_Syntax.lbpos
                                    in
                                 let uu____25172 =
                                   let uu____25173 =
                                     let uu____25184 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____25184]  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____25173;
                                     FStar_Syntax_Syntax.flags = []
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____25172)
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
                            let uu____25212 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____25226 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres  in
                            (uu____25212, uu____25226,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____25227 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____25238 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____25238
        then
          let universe_of_binders bs =
            let uu____25265 =
              FStar_List.fold_left
                (fun uu____25290  ->
                   fun b  ->
                     match uu____25290 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____25265 with | (uu____25338,us) -> FStar_List.rev us
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
            let uu___3234_25374 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3234_25374.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3234_25374.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3234_25374.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3234_25374.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3234_25374.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3234_25374.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3234_25374.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3234_25374.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3234_25374.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3234_25374.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3234_25374.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3234_25374.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3234_25374.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3234_25374.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3234_25374.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3234_25374.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___3234_25374.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___3234_25374.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3234_25374.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3234_25374.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3234_25374.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3234_25374.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3234_25374.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3234_25374.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3234_25374.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3234_25374.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3234_25374.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3234_25374.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3234_25374.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3234_25374.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3234_25374.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3234_25374.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3234_25374.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3234_25374.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3234_25374.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3234_25374.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3234_25374.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3234_25374.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3234_25374.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3234_25374.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3234_25374.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3234_25374.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3234_25374.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3234_25374.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3234_25374.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___3234_25374.FStar_TypeChecker_Env.enable_defer_to_tac)
            }  in
          let uu____25376 =
            let uu____25388 =
              let uu____25389 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____25389 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____25388 lb  in
          (match uu____25376 with
           | (e1,uu____25412,c1,g1,annotated) ->
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
                  (let uu____25426 =
                     let uu____25432 =
                       let uu____25434 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____25436 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____25434 uu____25436
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____25432)
                      in
                   FStar_Errors.raise_error uu____25426
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____25447 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ)
                      in
                   if uu____25447
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___3249_25459 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3249_25459.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3249_25459.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   }  in
                 let uu____25460 =
                   let uu____25465 =
                     let uu____25466 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____25466]  in
                   FStar_Syntax_Subst.open_term uu____25465 e2  in
                 match uu____25460 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____25510 =
                       let uu____25517 = tc_term env_x e21  in
                       FStar_All.pipe_right uu____25517
                         (fun uu____25543  ->
                            match uu____25543 with
                            | (e22,c2,g2) ->
                                let uu____25559 =
                                  let uu____25564 =
                                    FStar_All.pipe_right
                                      (fun uu____25582  ->
                                         "folding guard g2 of e2 in the lcomp")
                                      (fun uu____25588  ->
                                         FStar_Pervasives_Native.Some
                                           uu____25588)
                                     in
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    uu____25564 env_x e22 c2 g2
                                   in
                                (match uu____25559 with
                                 | (c21,g21) -> (e22, c21, g21)))
                        in
                     (match uu____25510 with
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
                            let uu____25616 =
                              let uu____25617 =
                                let uu____25631 =
                                  FStar_Syntax_Subst.close xb e23  in
                                ((false, [lb1]), uu____25631)  in
                              FStar_Syntax_Syntax.Tm_let uu____25617  in
                            FStar_Syntax_Syntax.mk uu____25616
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ
                             in
                          let g21 =
                            let uu____25649 =
                              let uu____25651 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2)
                                 in
                              FStar_All.pipe_right uu____25651
                                (FStar_TypeChecker_Env.is_layered_effect env2)
                               in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____25649 xb g2
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g21
                             in
                          let uu____25654 =
                            let uu____25656 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____25656  in
                          if uu____25654
                          then
                            let tt =
                              let uu____25667 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____25667
                                FStar_Option.get
                               in
                            ((let uu____25673 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____25673
                              then
                                let uu____25678 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____25680 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____25678 uu____25680
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____25687 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ
                                in
                             match uu____25687 with
                             | (t,g_ex) ->
                                 ((let uu____25701 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____25701
                                   then
                                     let uu____25706 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ
                                        in
                                     let uu____25708 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____25706 uu____25708
                                   else ());
                                  (let uu____25713 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___3288_25715 = cres  in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3288_25715.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3288_25715.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3288_25715.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____25713))))))))
      | uu____25716 ->
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
          let uu____25752 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25752 with
           | (lbs1,e21) ->
               let uu____25771 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25771 with
                | (env0,topt) ->
                    let uu____25790 = build_let_rec_env true env0 lbs1  in
                    (match uu____25790 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25813 = check_let_recs rec_env lbs2  in
                         (match uu____25813 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____25833 =
                                  let uu____25834 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____25834
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____25833
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____25840 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____25840
                                  (fun uu____25857  ->
                                     FStar_Pervasives_Native.Some uu____25857)
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
                                     let uu____25894 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____25928 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____25928)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____25894
                                      in
                                   FStar_List.map2
                                     (fun uu____25963  ->
                                        fun lb  ->
                                          match uu____25963 with
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
                                let uu____26011 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____26011
                                 in
                              let uu____26012 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____26012 with
                               | (lbs5,e22) ->
                                   ((let uu____26032 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____26032
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____26033 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____26033, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____26047 -> failwith "Impossible"

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
          let uu____26083 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____26083 with
           | (lbs1,e21) ->
               let uu____26102 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____26102 with
                | (env0,topt) ->
                    let uu____26121 = build_let_rec_env false env0 lbs1  in
                    (match uu____26121 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____26144 =
                           let uu____26151 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____26151
                             (fun uu____26174  ->
                                match uu____26174 with
                                | (lbs3,g) ->
                                    let uu____26193 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____26193))
                            in
                         (match uu____26144 with
                          | (lbs3,g_lbs) ->
                              let uu____26208 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3363_26231 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3363_26231.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3363_26231.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3366_26233 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3366_26233.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3366_26233.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3366_26233.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3366_26233.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3366_26233.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3366_26233.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____26208 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____26260 = tc_term env2 e21  in
                                   (match uu____26260 with
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
                                          let uu____26284 =
                                            let uu____26285 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____26285 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____26284
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
                                          let uu___3387_26295 = cres4  in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3387_26295.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3387_26295.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3387_26295.FStar_TypeChecker_Common.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____26303 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____26303))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard
                                           in
                                        let uu____26305 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____26305 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 top.FStar_Syntax_Syntax.pos
                                                in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____26346 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____26347 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____26347 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3403_26361
                                                           = cres5  in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3403_26361.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3403_26361.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3403_26361.FStar_TypeChecker_Common.comp_thunk)
                                                         }  in
                                                       let uu____26362 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____26362))))))))))
      | uu____26363 -> failwith "Impossible"

and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Common.guard_t))
  =
  fun _top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____26416 = FStar_Options.ml_ish ()  in
          if uu____26416
          then FStar_Pervasives_Native.None
          else
            (let lbtyp0 = lbtyp  in
             let uu____26434 = FStar_Syntax_Util.abs_formals lbdef  in
             match uu____26434 with
             | (actuals,body,body_lc) ->
                 let actuals1 =
                   let uu____26458 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp  in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____26458 actuals
                    in
                 let nactuals = FStar_List.length actuals1  in
                 let uu____26466 =
                   FStar_TypeChecker_Normalize.get_n_binders env nactuals
                     lbtyp
                    in
                 (match uu____26466 with
                  | (formals,c) ->
                      (if
                         (FStar_List.isEmpty formals) ||
                           (FStar_List.isEmpty actuals1)
                       then
                         (let uu____26494 =
                            let uu____26500 =
                              let uu____26502 =
                                FStar_Syntax_Print.term_to_string lbdef  in
                              let uu____26504 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              FStar_Util.format2
                                "Only function literals with arrow types can be defined recursively; got %s : %s"
                                uu____26502 uu____26504
                               in
                            (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                              uu____26500)
                             in
                          FStar_Errors.raise_error uu____26494
                            lbtyp.FStar_Syntax_Syntax.pos)
                       else ();
                       (let nformals = FStar_List.length formals  in
                        let uu____26511 =
                          let uu____26513 =
                            FStar_All.pipe_right
                              (FStar_Syntax_Util.comp_effect_name c)
                              (FStar_TypeChecker_Env.lookup_effect_quals env)
                             in
                          FStar_All.pipe_right uu____26513
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect)
                           in
                        if uu____26511
                        then
                          let uu____26529 =
                            let uu____26535 =
                              FStar_Syntax_Util.abs actuals1 body body_lc  in
                            (nformals, uu____26535)  in
                          FStar_Pervasives_Native.Some uu____26529
                        else FStar_Pervasives_Native.None))))
           in
        let uu____26549 =
          FStar_List.fold_left
            (fun uu____26583  ->
               fun lb  ->
                 match uu____26583 with
                 | (lbs1,env1,g_acc) ->
                     let uu____26608 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____26608 with
                      | (univ_vars,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____26631 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars
                                  in
                               let uu____26650 =
                                 let uu____26657 =
                                   let uu____26658 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____26658
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3443_26669 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3443_26669.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3443_26669.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3443_26669.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3443_26669.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3443_26669.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3443_26669.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3443_26669.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3443_26669.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3443_26669.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3443_26669.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3443_26669.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3443_26669.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3443_26669.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3443_26669.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3443_26669.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3443_26669.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___3443_26669.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3443_26669.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3443_26669.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3443_26669.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3443_26669.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3443_26669.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3443_26669.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3443_26669.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3443_26669.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3443_26669.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3443_26669.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3443_26669.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3443_26669.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3443_26669.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3443_26669.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3443_26669.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3443_26669.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3443_26669.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3443_26669.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3443_26669.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3443_26669.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3443_26669.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3443_26669.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3443_26669.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3443_26669.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3443_26669.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3443_26669.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3443_26669.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3443_26669.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___3443_26669.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }) t uu____26657 ""
                                  in
                               match uu____26650 with
                               | (t1,uu____26679,g) ->
                                   let uu____26681 =
                                     let uu____26682 =
                                       let uu____26683 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____26683
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____26682
                                      in
                                   let uu____26684 = norm env01 t1  in
                                   (uu____26681, uu____26684))
                             in
                          (match uu____26631 with
                           | (g,t1) ->
                               let uu____26703 =
                                 let uu____26708 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 match uu____26708 with
                                 | FStar_Pervasives_Native.Some (arity,def)
                                     ->
                                     let lb1 =
                                       let uu___3456_26730 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3456_26730.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3456_26730.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = def;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3456_26730.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3456_26730.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let env3 =
                                       let uu___3459_26732 = env2  in
                                       {
                                         FStar_TypeChecker_Env.solver =
                                           (uu___3459_26732.FStar_TypeChecker_Env.solver);
                                         FStar_TypeChecker_Env.range =
                                           (uu___3459_26732.FStar_TypeChecker_Env.range);
                                         FStar_TypeChecker_Env.curmodule =
                                           (uu___3459_26732.FStar_TypeChecker_Env.curmodule);
                                         FStar_TypeChecker_Env.gamma =
                                           (uu___3459_26732.FStar_TypeChecker_Env.gamma);
                                         FStar_TypeChecker_Env.gamma_sig =
                                           (uu___3459_26732.FStar_TypeChecker_Env.gamma_sig);
                                         FStar_TypeChecker_Env.gamma_cache =
                                           (uu___3459_26732.FStar_TypeChecker_Env.gamma_cache);
                                         FStar_TypeChecker_Env.modules =
                                           (uu___3459_26732.FStar_TypeChecker_Env.modules);
                                         FStar_TypeChecker_Env.expected_typ =
                                           (uu___3459_26732.FStar_TypeChecker_Env.expected_typ);
                                         FStar_TypeChecker_Env.sigtab =
                                           (uu___3459_26732.FStar_TypeChecker_Env.sigtab);
                                         FStar_TypeChecker_Env.attrtab =
                                           (uu___3459_26732.FStar_TypeChecker_Env.attrtab);
                                         FStar_TypeChecker_Env.instantiate_imp
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.instantiate_imp);
                                         FStar_TypeChecker_Env.effects =
                                           (uu___3459_26732.FStar_TypeChecker_Env.effects);
                                         FStar_TypeChecker_Env.generalize =
                                           (uu___3459_26732.FStar_TypeChecker_Env.generalize);
                                         FStar_TypeChecker_Env.letrecs =
                                           (((lb1.FStar_Syntax_Syntax.lbname),
                                              arity, t1, univ_vars) ::
                                           (env2.FStar_TypeChecker_Env.letrecs));
                                         FStar_TypeChecker_Env.top_level =
                                           (uu___3459_26732.FStar_TypeChecker_Env.top_level);
                                         FStar_TypeChecker_Env.check_uvars =
                                           (uu___3459_26732.FStar_TypeChecker_Env.check_uvars);
                                         FStar_TypeChecker_Env.use_eq =
                                           (uu___3459_26732.FStar_TypeChecker_Env.use_eq);
                                         FStar_TypeChecker_Env.use_eq_strict
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.use_eq_strict);
                                         FStar_TypeChecker_Env.is_iface =
                                           (uu___3459_26732.FStar_TypeChecker_Env.is_iface);
                                         FStar_TypeChecker_Env.admit =
                                           (uu___3459_26732.FStar_TypeChecker_Env.admit);
                                         FStar_TypeChecker_Env.lax =
                                           (uu___3459_26732.FStar_TypeChecker_Env.lax);
                                         FStar_TypeChecker_Env.lax_universes
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.lax_universes);
                                         FStar_TypeChecker_Env.phase1 =
                                           (uu___3459_26732.FStar_TypeChecker_Env.phase1);
                                         FStar_TypeChecker_Env.failhard =
                                           (uu___3459_26732.FStar_TypeChecker_Env.failhard);
                                         FStar_TypeChecker_Env.nosynth =
                                           (uu___3459_26732.FStar_TypeChecker_Env.nosynth);
                                         FStar_TypeChecker_Env.uvar_subtyping
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.uvar_subtyping);
                                         FStar_TypeChecker_Env.tc_term =
                                           (uu___3459_26732.FStar_TypeChecker_Env.tc_term);
                                         FStar_TypeChecker_Env.type_of =
                                           (uu___3459_26732.FStar_TypeChecker_Env.type_of);
                                         FStar_TypeChecker_Env.universe_of =
                                           (uu___3459_26732.FStar_TypeChecker_Env.universe_of);
                                         FStar_TypeChecker_Env.check_type_of
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.check_type_of);
                                         FStar_TypeChecker_Env.use_bv_sorts =
                                           (uu___3459_26732.FStar_TypeChecker_Env.use_bv_sorts);
                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.qtbl_name_and_index);
                                         FStar_TypeChecker_Env.normalized_eff_names
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.normalized_eff_names);
                                         FStar_TypeChecker_Env.fv_delta_depths
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.fv_delta_depths);
                                         FStar_TypeChecker_Env.proof_ns =
                                           (uu___3459_26732.FStar_TypeChecker_Env.proof_ns);
                                         FStar_TypeChecker_Env.synth_hook =
                                           (uu___3459_26732.FStar_TypeChecker_Env.synth_hook);
                                         FStar_TypeChecker_Env.try_solve_implicits_hook
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                         FStar_TypeChecker_Env.splice =
                                           (uu___3459_26732.FStar_TypeChecker_Env.splice);
                                         FStar_TypeChecker_Env.mpreprocess =
                                           (uu___3459_26732.FStar_TypeChecker_Env.mpreprocess);
                                         FStar_TypeChecker_Env.postprocess =
                                           (uu___3459_26732.FStar_TypeChecker_Env.postprocess);
                                         FStar_TypeChecker_Env.identifier_info
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.identifier_info);
                                         FStar_TypeChecker_Env.tc_hooks =
                                           (uu___3459_26732.FStar_TypeChecker_Env.tc_hooks);
                                         FStar_TypeChecker_Env.dsenv =
                                           (uu___3459_26732.FStar_TypeChecker_Env.dsenv);
                                         FStar_TypeChecker_Env.nbe =
                                           (uu___3459_26732.FStar_TypeChecker_Env.nbe);
                                         FStar_TypeChecker_Env.strict_args_tab
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.strict_args_tab);
                                         FStar_TypeChecker_Env.erasable_types_tab
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.erasable_types_tab);
                                         FStar_TypeChecker_Env.enable_defer_to_tac
                                           =
                                           (uu___3459_26732.FStar_TypeChecker_Env.enable_defer_to_tac)
                                       }  in
                                     (lb1, env3)
                                 | FStar_Pervasives_Native.None  ->
                                     let lb1 =
                                       let uu___3463_26749 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3463_26749.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3463_26749.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3463_26749.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3463_26749.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____26750 =
                                       FStar_TypeChecker_Env.push_let_binding
                                         env2 lb1.FStar_Syntax_Syntax.lbname
                                         (univ_vars, t1)
                                        in
                                     (lb1, uu____26750)
                                  in
                               (match uu____26703 with
                                | (lb1,env3) -> ((lb1 :: lbs1), env3, g)))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____26549 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____26790 =
        let uu____26799 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____26825 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____26825 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____26855 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____26855
                       | uu____26862 ->
                           let arity =
                             let uu____26866 =
                               FStar_TypeChecker_Env.get_letrec_arity env
                                 lb.FStar_Syntax_Syntax.lbname
                                in
                             match uu____26866 with
                             | FStar_Pervasives_Native.Some n -> n
                             | FStar_Pervasives_Native.None  ->
                                 FStar_List.length bs
                              in
                           let uu____26881 = FStar_List.splitAt arity bs  in
                           (match uu____26881 with
                            | (bs0,bs1) ->
                                let def =
                                  if FStar_List.isEmpty bs1
                                  then FStar_Syntax_Util.abs bs0 t lcomp
                                  else
                                    (let inner =
                                       FStar_Syntax_Util.abs bs1 t lcomp  in
                                     let inner1 =
                                       FStar_Syntax_Subst.close bs0 inner  in
                                     let bs01 =
                                       FStar_Syntax_Subst.close_binders bs0
                                        in
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_abs
                                          (bs01, inner1,
                                            FStar_Pervasives_Native.None))
                                       inner1.FStar_Syntax_Syntax.pos)
                                   in
                                let lb1 =
                                  let uu___3495_26978 = lb  in
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      (uu___3495_26978.FStar_Syntax_Syntax.lbname);
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___3495_26978.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp =
                                      (uu___3495_26978.FStar_Syntax_Syntax.lbtyp);
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___3495_26978.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___3495_26978.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___3495_26978.FStar_Syntax_Syntax.lbpos)
                                  }  in
                                let uu____26979 =
                                  let uu____26986 =
                                    FStar_TypeChecker_Env.set_expected_typ
                                      env lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  tc_tot_or_gtot_term uu____26986
                                    lb1.FStar_Syntax_Syntax.lbdef
                                   in
                                (match uu____26979 with
                                 | (e,c,g) ->
                                     ((let uu____26995 =
                                         let uu____26997 =
                                           FStar_TypeChecker_Common.is_total_lcomp
                                             c
                                            in
                                         Prims.op_Negation uu____26997  in
                                       if uu____26995
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
                                           FStar_Parser_Const.effect_Tot_lid
                                           e lb1.FStar_Syntax_Syntax.lbattrs
                                           lb1.FStar_Syntax_Syntax.lbpos
                                          in
                                       (lb2, g))))))))
           in
        FStar_All.pipe_right uu____26799 FStar_List.unzip  in
      match uu____26790 with
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
        let uu____27053 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____27053 with
        | (env1,uu____27072) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____27080 = check_lbtyp top_level env lb  in
            (match uu____27080 with
             | (topt,wf_annot,univ_vars,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____27129 =
                     tc_maybe_toplevel_term
                       (let uu___3526_27138 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3526_27138.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3526_27138.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3526_27138.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3526_27138.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3526_27138.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3526_27138.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3526_27138.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3526_27138.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3526_27138.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3526_27138.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3526_27138.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3526_27138.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3526_27138.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3526_27138.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3526_27138.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3526_27138.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___3526_27138.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3526_27138.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3526_27138.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3526_27138.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3526_27138.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3526_27138.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3526_27138.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3526_27138.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3526_27138.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3526_27138.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3526_27138.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3526_27138.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3526_27138.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3526_27138.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3526_27138.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3526_27138.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3526_27138.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3526_27138.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3526_27138.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3526_27138.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3526_27138.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3526_27138.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3526_27138.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3526_27138.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3526_27138.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3526_27138.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3526_27138.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3526_27138.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3526_27138.FStar_TypeChecker_Env.erasable_types_tab);
                          FStar_TypeChecker_Env.enable_defer_to_tac =
                            (uu___3526_27138.FStar_TypeChecker_Env.enable_defer_to_tac)
                        }) e11
                      in
                   match uu____27129 with
                   | (e12,c1,g1) ->
                       let uu____27153 =
                         let uu____27158 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____27164  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____27158 e12 c1 wf_annot
                          in
                       (match uu____27153 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____27181 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____27181
                              then
                                let uu____27184 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____27186 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11
                                   in
                                let uu____27188 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____27184 uu____27186 uu____27188
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
            let uu____27227 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____27227 with
             | (univ_opening,univ_vars) ->
                 let uu____27260 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars,
                   univ_opening, uu____27260))
        | uu____27265 ->
            let uu____27266 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____27266 with
             | (univ_opening,univ_vars) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____27316 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars,
                     univ_opening, uu____27316)
                 else
                   (let uu____27323 = FStar_Syntax_Util.type_u ()  in
                    match uu____27323 with
                    | (k,uu____27343) ->
                        let uu____27344 =
                          tc_check_tot_or_gtot_term env1 t1 k ""  in
                        (match uu____27344 with
                         | (t2,uu____27367,g) ->
                             ((let uu____27370 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____27370
                               then
                                 let uu____27373 =
                                   let uu____27375 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____27375
                                    in
                                 let uu____27376 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____27373 uu____27376
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____27382 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars, univ_opening, uu____27382))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____27388  ->
      match uu____27388 with
      | (x,imp) ->
          let uu____27415 = FStar_Syntax_Util.type_u ()  in
          (match uu____27415 with
           | (tu,u) ->
               ((let uu____27437 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____27437
                 then
                   let uu____27440 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____27442 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____27444 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____27440 uu____27442 uu____27444
                 else ());
                (let uu____27449 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu ""
                    in
                 match uu____27449 with
                 | (t,uu____27472,g) ->
                     let uu____27474 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau_or_attr) ->
                           (match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let uu____27497 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau
                                   in
                                (match uu____27497 with
                                 | (tau1,uu____27511,g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                               tau1))), g1))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let uu____27518 =
                                  tc_check_tot_or_gtot_term env attr
                                    FStar_Syntax_Syntax.t_unit ""
                                   in
                                (match uu____27518 with
                                 | (attr1,uu____27533,g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                               attr1))),
                                       FStar_TypeChecker_Env.trivial_guard)))
                       | uu____27537 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____27474 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3596_27572 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3596_27572.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3596_27572.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____27574 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____27574
                            then
                              let uu____27577 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____27581 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____27577
                                uu____27581
                            else ());
                           (let uu____27586 = push_binding env x1  in
                            (x1, uu____27586, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____27598 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____27598
       then
         let uu____27601 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____27601
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____27714 = tc_binder env1 b  in
             (match uu____27714 with
              | (b1,env',g,u) ->
                  let uu____27763 = aux env' bs2  in
                  (match uu____27763 with
                   | (bs3,env'1,g',us) ->
                       let uu____27824 =
                         let uu____27825 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____27825  in
                       ((b1 :: bs3), env'1, uu____27824, (u :: us))))
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
          (fun uu____27933  ->
             fun uu____27934  ->
               match (uu____27933, uu____27934) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____28026 = tc_term en1 t  in
                     match uu____28026 with
                     | (t1,uu____28046,g') ->
                         let uu____28048 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____28048)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____28102  ->
             match uu____28102 with
             | (pats1,g) ->
                 let uu____28129 = tc_args en p  in
                 (match uu____28129 with
                  | (args,g') ->
                      let uu____28142 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____28142))) pats
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
        let uu____28157 = tc_maybe_toplevel_term env e  in
        match uu____28157 with
        | (e1,c,g) ->
            let uu____28173 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c
               in
            if uu____28173
            then (e1, c, g)
            else
              (let g1 =
                 FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
               let uu____28185 = FStar_TypeChecker_Common.lcomp_comp c  in
               match uu____28185 with
               | (c1,g_c) ->
                   let c2 = norm_c env c1  in
                   let uu____28199 =
                     let uu____28205 =
                       FStar_TypeChecker_Util.is_pure_effect env
                         (FStar_Syntax_Util.comp_effect_name c2)
                        in
                     if uu____28205
                     then
                       let uu____28213 =
                         FStar_Syntax_Syntax.mk_Total
                           (FStar_Syntax_Util.comp_result c2)
                          in
                       (uu____28213, false)
                     else
                       (let uu____28218 =
                          FStar_Syntax_Syntax.mk_GTotal
                            (FStar_Syntax_Util.comp_result c2)
                           in
                        (uu____28218, true))
                      in
                   (match uu____28199 with
                    | (target_comp,allow_ghost) ->
                        let uu____28231 =
                          FStar_TypeChecker_Rel.sub_comp env c2 target_comp
                           in
                        (match uu____28231 with
                         | FStar_Pervasives_Native.Some g' ->
                             let uu____28241 =
                               FStar_TypeChecker_Common.lcomp_of_comp
                                 target_comp
                                in
                             let uu____28242 =
                               let uu____28243 =
                                 FStar_TypeChecker_Env.conj_guard g_c g'  in
                               FStar_TypeChecker_Env.conj_guard g1
                                 uu____28243
                                in
                             (e1, uu____28241, uu____28242)
                         | uu____28244 ->
                             if allow_ghost
                             then
                               let uu____28254 =
                                 FStar_TypeChecker_Err.expected_ghost_expression
                                   e1 c2 msg
                                  in
                               FStar_Errors.raise_error uu____28254
                                 e1.FStar_Syntax_Syntax.pos
                             else
                               (let uu____28268 =
                                  FStar_TypeChecker_Err.expected_pure_expression
                                    e1 c2 msg
                                   in
                                FStar_Errors.raise_error uu____28268
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
      let uu____28297 = tc_tot_or_gtot_term env t  in
      match uu____28297 with
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
        let uu____28328 = tc_check_tot_or_gtot_term env t k ""  in
        match uu____28328 with
        | (t1,uu____28337,g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____28358 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____28358
       then
         let uu____28363 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____28363
       else ());
      (let env1 =
         let uu___3692_28369 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3692_28369.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3692_28369.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3692_28369.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3692_28369.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3692_28369.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3692_28369.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3692_28369.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3692_28369.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3692_28369.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3692_28369.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3692_28369.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3692_28369.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3692_28369.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3692_28369.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3692_28369.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___3692_28369.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___3692_28369.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3692_28369.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3692_28369.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3692_28369.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3692_28369.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3692_28369.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3692_28369.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3692_28369.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3692_28369.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3692_28369.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3692_28369.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3692_28369.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3692_28369.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3692_28369.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3692_28369.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3692_28369.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3692_28369.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3692_28369.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3692_28369.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3692_28369.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3692_28369.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3692_28369.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3692_28369.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3692_28369.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3692_28369.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3692_28369.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3692_28369.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3692_28369.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___3692_28369.FStar_TypeChecker_Env.enable_defer_to_tac)
         }  in
       let uu____28380 =
         try
           (fun uu___3696_28394  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____28415) ->
             let uu____28418 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____28418
          in
       match uu____28380 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____28436 = FStar_TypeChecker_Common.is_total_lcomp c1  in
           if uu____28436
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____28447 =
                let uu____28453 =
                  let uu____28455 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____28455
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____28453)
                 in
              let uu____28459 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____28447 uu____28459))
  
let level_of_type_fail :
  'uuuuuu28475 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'uuuuuu28475
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____28493 =
          let uu____28499 =
            let uu____28501 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____28501 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____28499)  in
        let uu____28505 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____28493 uu____28505
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____28539 =
            let uu____28540 = FStar_Syntax_Util.unrefine t1  in
            uu____28540.FStar_Syntax_Syntax.n  in
          match uu____28539 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____28544 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____28550 = FStar_Syntax_Util.type_u ()  in
                 match uu____28550 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3728_28558 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3728_28558.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3728_28558.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3728_28558.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3728_28558.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3728_28558.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3728_28558.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3728_28558.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3728_28558.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3728_28558.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3728_28558.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3728_28558.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3728_28558.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3728_28558.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3728_28558.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3728_28558.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3728_28558.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3728_28558.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3728_28558.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3728_28558.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3728_28558.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3728_28558.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3728_28558.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3728_28558.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3728_28558.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3728_28558.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3728_28558.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3728_28558.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3728_28558.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3728_28558.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3728_28558.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3728_28558.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3728_28558.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3728_28558.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3728_28558.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3728_28558.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3728_28558.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3728_28558.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3728_28558.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3728_28558.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3728_28558.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3728_28558.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3728_28558.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3728_28558.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3728_28558.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3728_28558.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3728_28558.FStar_TypeChecker_Env.enable_defer_to_tac)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____28563 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____28563
                       | uu____28565 ->
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
      let uu____28582 =
        let uu____28583 = FStar_Syntax_Subst.compress e  in
        uu____28583.FStar_Syntax_Syntax.n  in
      match uu____28582 with
      | FStar_Syntax_Syntax.Tm_bvar uu____28586 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____28589 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____28605 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____28622) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____28667) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____28674 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____28674 with | ((uu____28683,t),uu____28685) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____28691 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____28691
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28694,(FStar_Util.Inl t,uu____28696),uu____28697) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28744,(FStar_Util.Inr c,uu____28746),uu____28747) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____28795 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____28804;
             FStar_Syntax_Syntax.vars = uu____28805;_},us)
          ->
          let uu____28811 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____28811 with
           | ((us',t),uu____28822) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____28829 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____28829)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____28850 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____28852 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____28861) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____28888 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____28888 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____28908  ->
                      match uu____28908 with
                      | (b,uu____28916) ->
                          let uu____28921 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____28921) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____28926 = universe_of_aux env res  in
                 level_of_type env res uu____28926  in
               let u_c =
                 FStar_All.pipe_right c1
                   (FStar_TypeChecker_Util.universe_of_comp env u_res)
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let rec type_of_head retry hd1 args1 =
            let hd2 = FStar_Syntax_Subst.compress hd1  in
            match hd2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____29037 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____29053 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____29083 ->
                let uu____29084 = universe_of_aux env hd2  in
                (uu____29084, args1)
            | FStar_Syntax_Syntax.Tm_name uu____29095 ->
                let uu____29096 = universe_of_aux env hd2  in
                (uu____29096, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____29107 ->
                let uu____29120 = universe_of_aux env hd2  in
                (uu____29120, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____29131 ->
                let uu____29138 = universe_of_aux env hd2  in
                (uu____29138, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____29149 ->
                let uu____29176 = universe_of_aux env hd2  in
                (uu____29176, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____29187 ->
                let uu____29194 = universe_of_aux env hd2  in
                (uu____29194, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____29205 ->
                let uu____29206 = universe_of_aux env hd2  in
                (uu____29206, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____29217 ->
                let uu____29232 = universe_of_aux env hd2  in
                (uu____29232, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____29243 ->
                let uu____29250 = universe_of_aux env hd2  in
                (uu____29250, args1)
            | FStar_Syntax_Syntax.Tm_type uu____29261 ->
                let uu____29262 = universe_of_aux env hd2  in
                (uu____29262, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____29273,hd3::uu____29275) ->
                let uu____29340 = FStar_Syntax_Subst.open_branch hd3  in
                (match uu____29340 with
                 | (uu____29355,uu____29356,hd4) ->
                     let uu____29374 = FStar_Syntax_Util.head_and_args hd4
                        in
                     (match uu____29374 with
                      | (hd5,args') ->
                          type_of_head retry hd5
                            (FStar_List.append args' args1)))
            | uu____29439 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____29441 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____29441 with
                 | (hd3,args2) -> type_of_head false hd3 args2)
            | uu____29499 ->
                let uu____29500 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____29500 with
                 | (env1,uu____29522) ->
                     let env2 =
                       let uu___3889_29528 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3889_29528.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3889_29528.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3889_29528.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3889_29528.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3889_29528.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3889_29528.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3889_29528.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3889_29528.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3889_29528.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3889_29528.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3889_29528.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3889_29528.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3889_29528.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3889_29528.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3889_29528.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3889_29528.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3889_29528.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3889_29528.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3889_29528.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3889_29528.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3889_29528.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3889_29528.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3889_29528.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3889_29528.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3889_29528.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3889_29528.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3889_29528.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3889_29528.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3889_29528.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3889_29528.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3889_29528.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3889_29528.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3889_29528.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3889_29528.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3889_29528.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3889_29528.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3889_29528.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3889_29528.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3889_29528.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3889_29528.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3889_29528.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3889_29528.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3889_29528.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3889_29528.FStar_TypeChecker_Env.enable_defer_to_tac)
                       }  in
                     ((let uu____29533 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____29533
                       then
                         let uu____29538 =
                           let uu____29540 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____29540  in
                         let uu____29541 =
                           FStar_Syntax_Print.term_to_string hd2  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____29538 uu____29541
                       else ());
                      (let uu____29546 = tc_term env2 hd2  in
                       match uu____29546 with
                       | (uu____29567,{
                                        FStar_TypeChecker_Common.eff_name =
                                          uu____29568;
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          uu____29570;
                                        FStar_TypeChecker_Common.comp_thunk =
                                          uu____29571;_},g)
                           ->
                           ((let uu____29589 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____29589
                               (fun uu____29590  -> ()));
                            (t, args1)))))
             in
          let uu____29601 = type_of_head true hd args  in
          (match uu____29601 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____29640 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____29640 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst res1
                    else
                      (let uu____29668 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____29668)))
      | FStar_Syntax_Syntax.Tm_match (uu____29670,hd::uu____29672) ->
          let uu____29737 = FStar_Syntax_Subst.open_branch hd  in
          (match uu____29737 with
           | (uu____29738,uu____29739,hd1) -> universe_of_aux env hd1)
      | FStar_Syntax_Syntax.Tm_match (uu____29757,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____29804 = universe_of_aux env e  in
      level_of_type env e uu____29804
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env0  ->
    fun tps  ->
      let uu____29828 = tc_binders env0 tps  in
      match uu____29828 with
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
          t.FStar_Syntax_Syntax.pos
         in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____29886 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____29904 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____29910 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____29910
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____29912 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29912
            (fun uu____29926  ->
               match uu____29926 with
               | (t2,uu____29934) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____29936;
             FStar_Syntax_Syntax.vars = uu____29937;_},us)
          ->
          let uu____29943 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29943
            (fun uu____29957  ->
               match uu____29957 with
               | (t2,uu____29965) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____29966) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____29968 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____29968
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____29970 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____29970
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____29975;_})
          ->
          let mk_comp =
            let uu____30019 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____30019
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____30050 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____30050
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____30120 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____30120
                 (fun u  ->
                    let uu____30128 =
                      let uu____30131 =
                        let uu____30132 =
                          let uu____30147 =
                            f tbody (FStar_Pervasives_Native.Some u)  in
                          (bs, uu____30147)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____30132  in
                      FStar_Syntax_Syntax.mk uu____30131
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____30128))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____30184 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____30184 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____30243 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____30243
                       (fun uc  ->
                          let uu____30251 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____30251)
                 | (x,imp)::bs3 ->
                     let uu____30277 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____30277
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____30286 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____30306) ->
          let uu____30311 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____30311
            (fun u_x  ->
               let uu____30319 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____30319)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____30324;
             FStar_Syntax_Syntax.vars = uu____30325;_},a::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____30404 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____30404 with
           | (unary_op,uu____30424) ->
               let head =
                 let uu____30452 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____30452
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____30500;
             FStar_Syntax_Syntax.vars = uu____30501;_},a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____30597 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____30597 with
           | (unary_op,uu____30617) ->
               let head =
                 let uu____30645 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   uu____30645
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____30701;
             FStar_Syntax_Syntax.vars = uu____30702;_},uu____30703::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____30742;
             FStar_Syntax_Syntax.vars = uu____30743;_},(t2,uu____30745)::uu____30746::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let t_hd = type_of_well_typed_term env hd  in
          let rec aux t_hd1 =
            let uu____30842 =
              let uu____30843 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____30843.FStar_Syntax_Syntax.n  in
            match uu____30842 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____30916 = FStar_Util.first_N n_args bs  in
                    match uu____30916 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____31004 =
                          let uu____31009 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____31009  in
                        (match uu____31004 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____31063 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____31063 with
                       | (bs1,c1) ->
                           let uu____31084 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____31084
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____31166  ->
                     match uu____31166 with
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
                         let uu____31242 = FStar_Syntax_Subst.subst subst t2
                            in
                         FStar_Pervasives_Native.Some uu____31242)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____31244) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____31250,uu____31251) ->
                aux t2
            | uu____31292 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____31293,(FStar_Util.Inl t2,uu____31295),uu____31296) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____31343,(FStar_Util.Inr c,uu____31345),uu____31346) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____31411 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____31411
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____31419) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____31424 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____31447 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____31461 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____31472 = type_of_well_typed_term env t  in
      match uu____31472 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____31478;
            FStar_Syntax_Syntax.vars = uu____31479;_}
          -> FStar_Pervasives_Native.Some u
      | uu____31482 -> FStar_Pervasives_Native.None

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
            let uu___4168_31510 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4168_31510.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4168_31510.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4168_31510.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4168_31510.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4168_31510.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4168_31510.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4168_31510.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4168_31510.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4168_31510.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4168_31510.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4168_31510.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4168_31510.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4168_31510.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4168_31510.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4168_31510.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4168_31510.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4168_31510.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4168_31510.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4168_31510.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4168_31510.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4168_31510.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4168_31510.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4168_31510.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4168_31510.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4168_31510.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4168_31510.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4168_31510.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4168_31510.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4168_31510.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4168_31510.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4168_31510.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4168_31510.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4168_31510.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4168_31510.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4168_31510.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4168_31510.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4168_31510.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4168_31510.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4168_31510.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4168_31510.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4168_31510.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4168_31510.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4168_31510.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4168_31510.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4168_31510.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4168_31510.FStar_TypeChecker_Env.enable_defer_to_tac)
            }  in
          let slow_check uu____31517 =
            if must_total
            then
              let uu____31519 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____31519 with | (uu____31526,uu____31527,g) -> g
            else
              (let uu____31531 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____31531 with | (uu____31538,uu____31539,g) -> g)
             in
          let uu____31541 = type_of_well_typed_term env2 t  in
          match uu____31541 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____31546 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____31546
                then
                  let uu____31551 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____31553 = FStar_Syntax_Print.term_to_string t  in
                  let uu____31555 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____31557 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____31551 uu____31553 uu____31555 uu____31557
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____31566 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____31566
                 then
                   let uu____31571 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____31573 = FStar_Syntax_Print.term_to_string t  in
                   let uu____31575 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____31577 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____31571
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____31573 uu____31575 uu____31577
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
            let uu___4199_31614 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4199_31614.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4199_31614.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4199_31614.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4199_31614.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4199_31614.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4199_31614.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4199_31614.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4199_31614.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4199_31614.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4199_31614.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4199_31614.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4199_31614.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4199_31614.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4199_31614.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4199_31614.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4199_31614.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4199_31614.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4199_31614.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4199_31614.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4199_31614.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4199_31614.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4199_31614.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4199_31614.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4199_31614.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4199_31614.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4199_31614.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4199_31614.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4199_31614.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4199_31614.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4199_31614.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4199_31614.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4199_31614.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4199_31614.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4199_31614.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4199_31614.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4199_31614.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4199_31614.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4199_31614.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4199_31614.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4199_31614.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4199_31614.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4199_31614.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4199_31614.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4199_31614.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4199_31614.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4199_31614.FStar_TypeChecker_Env.enable_defer_to_tac)
            }  in
          let slow_check uu____31621 =
            if must_total
            then
              let uu____31623 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____31623 with | (uu____31630,uu____31631,g) -> g
            else
              (let uu____31635 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____31635 with | (uu____31642,uu____31643,g) -> g)
             in
          let uu____31645 =
            let uu____31647 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____31647  in
          if uu____31645
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  