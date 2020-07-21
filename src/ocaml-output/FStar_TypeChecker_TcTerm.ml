open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env ->
    let uu___8_5 = env in
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
  fun env ->
    let uu___11_11 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___11_11.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___11_11.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___11_11.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___11_11.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___11_11.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___11_11.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___11_11.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___11_11.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___11_11.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___11_11.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___11_11.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___11_11.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___11_11.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___11_11.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___11_11.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___11_11.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.use_eq_strict =
        (uu___11_11.FStar_TypeChecker_Env.use_eq_strict);
      FStar_TypeChecker_Env.is_iface =
        (uu___11_11.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___11_11.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___11_11.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___11_11.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___11_11.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___11_11.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___11_11.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___11_11.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___11_11.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___11_11.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___11_11.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___11_11.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___11_11.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___11_11.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___11_11.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___11_11.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___11_11.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___11_11.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.try_solve_implicits_hook =
        (uu___11_11.FStar_TypeChecker_Env.try_solve_implicits_hook);
      FStar_TypeChecker_Env.splice =
        (uu___11_11.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.mpreprocess =
        (uu___11_11.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___11_11.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.identifier_info =
        (uu___11_11.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___11_11.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___11_11.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___11_11.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___11_11.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___11_11.FStar_TypeChecker_Env.erasable_types_tab);
      FStar_TypeChecker_Env.enable_defer_to_tac =
        (uu___11_11.FStar_TypeChecker_Env.enable_defer_to_tac)
    }
let (mk_lex_list :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun vs ->
    FStar_List.fold_right
      (fun v ->
         fun tl ->
           let r =
             if tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos
                 tl.FStar_Syntax_Syntax.pos in
           let uu____43 =
             let uu____44 = FStar_Syntax_Syntax.as_arg v in
             let uu____53 =
               let uu____64 = FStar_Syntax_Syntax.as_arg tl in [uu____64] in
             uu____44 :: uu____53 in
           FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____43
             r) vs FStar_Syntax_Util.lex_top
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___0_103 ->
    match uu___0_103 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> true
    | uu____106 -> false
let steps : 'uuuuuu113 . 'uuuuuu113 -> FStar_TypeChecker_Env.step Prims.list
  =
  fun env ->
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.NoFullNorm]
let (norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env -> fun t -> FStar_TypeChecker_Normalize.normalize (steps env) env t
let (norm_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun c -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
let (check_no_escape :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun head_opt ->
    fun env ->
      fun fvs ->
        fun kt ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____196 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____208 =
                  FStar_List.tryFind (fun x -> FStar_Util.set_mem x fvs') fvs in
                (match uu____208 with
                 | FStar_Pervasives_Native.None ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____232 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None ->
                                let uu____234 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____234
                            | FStar_Pervasives_Native.Some head ->
                                let uu____236 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____237 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____236 uu____237 in
                          let uu____238 = FStar_TypeChecker_Env.get_range env in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____238 in
                        let uu____243 =
                          let uu____256 = FStar_TypeChecker_Env.get_range env in
                          let uu____257 =
                            let uu____258 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____258 in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____256 env uu____257 in
                        match uu____243 with
                        | (s, uu____272, g0) ->
                            let uu____286 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s in
                            (match uu____286 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____295 =
                                     FStar_TypeChecker_Env.conj_guard g g0 in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____295 in
                                 (s, g1)
                             | uu____296 -> fail ()))) in
          aux false kt
let push_binding :
  'uuuuuu305 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu305) -> FStar_TypeChecker_Env.env
  =
  fun env ->
    fun b ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s ->
    fun b ->
      fun v ->
        let uu____359 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____359
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v)) ::
          s
let (set_lcomp_result :
  FStar_TypeChecker_Common.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_TypeChecker_Common.lcomp)
  =
  fun lc ->
    fun t ->
      FStar_TypeChecker_Common.apply_lcomp
        (fun c -> FStar_Syntax_Util.set_result_typ c t) (fun g -> g)
        (let uu___66_385 = lc in
         {
           FStar_TypeChecker_Common.eff_name =
             (uu___66_385.FStar_TypeChecker_Common.eff_name);
           FStar_TypeChecker_Common.res_typ = t;
           FStar_TypeChecker_Common.cflags =
             (uu___66_385.FStar_TypeChecker_Common.cflags);
           FStar_TypeChecker_Common.comp_thunk =
             (uu___66_385.FStar_TypeChecker_Common.comp_thunk)
         })
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> e
let (maybe_warn_on_use :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv -> unit) =
  fun env ->
    fun fv ->
      let uu____406 =
        FStar_TypeChecker_Env.lookup_attrs_of_lid env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      match uu____406 with
      | FStar_Pervasives_Native.None -> ()
      | FStar_Pervasives_Native.Some attrs ->
          FStar_All.pipe_right attrs
            (FStar_List.iter
               (fun a ->
                  let uu____429 = FStar_Syntax_Util.head_and_args a in
                  match uu____429 with
                  | (head, args) ->
                      let msg_arg m =
                        match args with
                        | ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_string (s, uu____479));
                             FStar_Syntax_Syntax.pos = uu____480;
                             FStar_Syntax_Syntax.vars = uu____481;_},
                           uu____482)::[] ->
                            Prims.op_Hat m (Prims.op_Hat ": " s)
                        | uu____507 -> m in
                      (match head.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar attr_fv when
                           FStar_Ident.lid_equals
                             (attr_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.warn_on_use_attr
                           ->
                           let m =
                             let uu____520 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             FStar_Util.format1
                               "Every use of %s triggers a warning" uu____520 in
                           let uu____521 =
                             FStar_Ident.range_of_lid
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                           FStar_Errors.log_issue uu____521
                             (FStar_Errors.Warning_WarnOnUse, (msg_arg m))
                       | FStar_Syntax_Syntax.Tm_fvar attr_fv when
                           FStar_Ident.lid_equals
                             (attr_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let m =
                             let uu____524 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             FStar_Util.format1 "%s is deprecated" uu____524 in
                           let uu____525 =
                             FStar_Ident.range_of_lid
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                           FStar_Errors.log_issue uu____525
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               (msg_arg m))
                       | uu____526 -> ())))
let (value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_TypeChecker_Common.lcomp)
        FStar_Util.either ->
        FStar_TypeChecker_Common.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun tlc ->
        fun guard ->
          FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos
            "value_check_expected_typ" env guard;
          (let lc =
             match tlc with
             | FStar_Util.Inl t ->
                 let uu____570 = FStar_Syntax_Syntax.mk_Total t in
                 FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                   uu____570
             | FStar_Util.Inr lc -> lc in
           let t = lc.FStar_TypeChecker_Common.res_typ in
           let uu____573 =
             let uu____580 = FStar_TypeChecker_Env.expected_typ env in
             match uu____580 with
             | FStar_Pervasives_Native.None -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____590 =
                   FStar_TypeChecker_Util.check_has_type env e lc t' in
                 (match uu____590 with
                  | (e1, lc1, g) ->
                      ((let uu____607 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Medium in
                        if uu____607
                        then
                          let uu____608 =
                            FStar_TypeChecker_Common.lcomp_to_string lc1 in
                          let uu____609 =
                            FStar_Syntax_Print.term_to_string t' in
                          let uu____610 =
                            FStar_TypeChecker_Rel.guard_to_string env g in
                          let uu____611 =
                            FStar_TypeChecker_Rel.guard_to_string env guard in
                          FStar_Util.print4
                            "value_check_expected_typ: type is %s<:%s \tguard is %s, %s\n"
                            uu____608 uu____609 uu____610 uu____611
                        else ());
                       (let t1 = lc1.FStar_TypeChecker_Common.res_typ in
                        let g1 = FStar_TypeChecker_Env.conj_guard g guard in
                        let msg =
                          let uu____621 =
                            FStar_TypeChecker_Env.is_trivial_guard_formula g1 in
                          if uu____621
                          then FStar_Pervasives_Native.None
                          else
                            FStar_All.pipe_left
                              (fun uu____642 ->
                                 FStar_Pervasives_Native.Some uu____642)
                              (FStar_TypeChecker_Err.subtyping_failed env t1
                                 t') in
                        let uu____643 =
                          FStar_TypeChecker_Util.strengthen_precondition msg
                            env e1 lc1 g1 in
                        match uu____643 with
                        | (lc2, g2) ->
                            let uu____656 = set_lcomp_result lc2 t' in
                            ((memo_tk e1 t'), uu____656, g2)))) in
           match uu____573 with | (e1, lc1, g) -> (e1, lc1, g))
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun lc ->
        let uu____693 = FStar_TypeChecker_Env.expected_typ env in
        match uu____693 with
        | FStar_Pervasives_Native.None ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____703 = FStar_TypeChecker_Util.maybe_coerce_lc env e lc t in
            (match uu____703 with
             | (e1, lc1, g_c) ->
                 let uu____719 =
                   FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t in
                 (match uu____719 with
                  | (e2, lc2, g) ->
                      let uu____735 = FStar_TypeChecker_Env.conj_guard g g_c in
                      (e2, lc2, uu____735)))
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun copt ->
      fun ec ->
        let uu____775 = ec in
        match uu____775 with
        | (e, c) ->
            let tot_or_gtot c1 =
              let uu____798 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____798
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____800 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____800
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____802 =
              let ct = FStar_Syntax_Util.comp_result c in
              match copt with
              | FStar_Pervasives_Native.Some uu____826 ->
                  (copt, c, FStar_Pervasives_Native.None)
              | FStar_Pervasives_Native.None ->
                  let uu____831 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____833 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____833)) in
                  if uu____831
                  then
                    let uu____844 =
                      let uu____847 =
                        FStar_Syntax_Util.ml_comp ct
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____847 in
                    (uu____844, c, FStar_Pervasives_Native.None)
                  else
                    (let uu____853 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____853
                     then
                       let uu____864 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____864,
                         FStar_Pervasives_Native.None)
                     else
                       (let uu____870 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____870
                        then
                          let uu____881 =
                            let uu____884 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____884 in
                          (uu____881, c, FStar_Pervasives_Native.None)
                        else
                          (let uu____890 =
                             let uu____891 =
                               FStar_All.pipe_right
                                 (FStar_Syntax_Util.comp_effect_name c)
                                 (FStar_TypeChecker_Env.norm_eff_name env) in
                             FStar_All.pipe_right uu____891
                               (FStar_TypeChecker_Env.is_layered_effect env) in
                           if uu____890
                           then
                             let uu____902 =
                               let uu____907 =
                                 let uu____908 =
                                   let uu____909 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name in
                                   FStar_All.pipe_right uu____909
                                     FStar_Ident.string_of_lid in
                                 let uu____912 =
                                   FStar_Range.string_of_range
                                     e.FStar_Syntax_Syntax.pos in
                                 FStar_Util.format2
                                   "Missing annotation for a layered effect (%s) computation at %s"
                                   uu____908 uu____912 in
                               (FStar_Errors.Fatal_IllTyped, uu____907) in
                             FStar_Errors.raise_error uu____902
                               e.FStar_Syntax_Syntax.pos
                           else
                             (let uu____924 =
                                FStar_Options.trivial_pre_for_unannotated_effectful_fns
                                  () in
                              if uu____924
                              then
                                let uu____935 =
                                  let uu____938 =
                                    FStar_TypeChecker_Util.check_trivial_precondition
                                      env c in
                                  match uu____938 with
                                  | (uu____947, uu____948, g) ->
                                      FStar_Pervasives_Native.Some g in
                                (FStar_Pervasives_Native.None, c, uu____935)
                              else
                                (FStar_Pervasives_Native.None, c,
                                  FStar_Pervasives_Native.None))))) in
            (match uu____802 with
             | (expected_c_opt, c1, gopt) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None ->
                      (e, c2,
                        ((match gopt with
                          | FStar_Pervasives_Native.None ->
                              FStar_TypeChecker_Env.trivial_guard
                          | FStar_Pervasives_Native.Some g -> g)))
                  | FStar_Pervasives_Native.Some expected_c ->
                      ((match gopt with
                        | FStar_Pervasives_Native.None -> ()
                        | FStar_Pervasives_Native.Some uu____986 ->
                            failwith
                              "Impossible! check_expected_effect, gopt should have been None");
                       (let c3 =
                          let uu____988 =
                            FStar_TypeChecker_Common.lcomp_of_comp c2 in
                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                            env e uu____988 in
                        let uu____989 =
                          FStar_TypeChecker_Common.lcomp_comp c3 in
                        match uu____989 with
                        | (c4, g_c) ->
                            ((let uu____1003 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Medium in
                              if uu____1003
                              then
                                let uu____1004 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____1005 =
                                  FStar_Syntax_Print.comp_to_string c4 in
                                let uu____1006 =
                                  FStar_Syntax_Print.comp_to_string
                                    expected_c in
                                FStar_Util.print3
                                  "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                                  uu____1004 uu____1005 uu____1006
                              else ());
                             (let uu____1008 =
                                FStar_TypeChecker_Util.check_comp env e c4
                                  expected_c in
                              match uu____1008 with
                              | (e1, uu____1022, g) ->
                                  let g1 =
                                    let uu____1025 =
                                      FStar_TypeChecker_Env.get_range env in
                                    FStar_TypeChecker_Util.label_guard
                                      uu____1025
                                      "could not prove post-condition" g in
                                  ((let uu____1027 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Medium in
                                    if uu____1027
                                    then
                                      let uu____1028 =
                                        FStar_Range.string_of_range
                                          e1.FStar_Syntax_Syntax.pos in
                                      let uu____1029 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          env g1 in
                                      FStar_Util.print2
                                        "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                        uu____1028 uu____1029
                                    else ());
                                   (let e2 =
                                      FStar_TypeChecker_Util.maybe_lift env
                                        e1
                                        (FStar_Syntax_Util.comp_effect_name
                                           c4)
                                        (FStar_Syntax_Util.comp_effect_name
                                           expected_c)
                                        (FStar_Syntax_Util.comp_result c4) in
                                    let uu____1032 =
                                      FStar_TypeChecker_Env.conj_guard g_c g1 in
                                    (e2, expected_c, uu____1032)))))))))
let no_logical_guard :
  'uuuuuu1041 'uuuuuu1042 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1041 * 'uuuuuu1042 * FStar_TypeChecker_Env.guard_t) ->
        ('uuuuuu1041 * 'uuuuuu1042 * FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun uu____1064 ->
      match uu____1064 with
      | (te, kt, f) ->
          let uu____1074 = FStar_TypeChecker_Env.guard_form f in
          (match uu____1074 with
           | FStar_TypeChecker_Common.Trivial -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____1082 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____1087 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____1082 uu____1087)
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu____1099 = FStar_TypeChecker_Env.expected_typ env in
    match uu____1099 with
    | FStar_Pervasives_Native.None ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____1103 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____1103
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all ->
    fun andlist ->
      fun pats ->
        let pats1 = FStar_Syntax_Util.unmeta pats in
        let uu____1128 = FStar_Syntax_Util.head_and_args pats1 in
        match uu____1128 with
        | (head, args) ->
            let uu____1173 =
              let uu____1188 =
                let uu____1189 = FStar_Syntax_Util.un_uinst head in
                uu____1189.FStar_Syntax_Syntax.n in
              (uu____1188, args) in
            (match uu____1173 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1205) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____1230, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____1231))::(hd,
                                                              FStar_Pervasives_Native.None)::
                (tl, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let hdvs = get_pat_vars' all false hd in
                 let tlvs = get_pat_vars' all andlist tl in
                 if andlist
                 then FStar_Util.set_intersect hdvs tlvs
                 else FStar_Util.set_union hdvs tlvs
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____1304, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____1305))::(pat,
                                                              FStar_Pervasives_Native.None)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> FStar_Syntax_Free.names pat
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (subpats, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> get_pat_vars' all true subpats
             | uu____1387 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
let (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all -> fun pats -> get_pat_vars' all false pats
let check_pat_fvs :
  'uuuuuu1428 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'uuuuuu1428) Prims.list -> unit
  =
  fun rng ->
    fun env ->
      fun pats ->
        fun bs ->
          let pat_vars =
            let uu____1464 = FStar_List.map FStar_Pervasives_Native.fst bs in
            let uu____1471 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats in
            get_pat_vars uu____1464 uu____1471 in
          let uu____1472 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1499 ->
                    match uu____1499 with
                    | (b, uu____1505) ->
                        let uu____1506 = FStar_Util.set_mem b pat_vars in
                        Prims.op_Negation uu____1506)) in
          match uu____1472 with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some (x, uu____1512) ->
              let uu____1517 =
                let uu____1522 =
                  let uu____1523 = FStar_Syntax_Print.bv_to_string x in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1523 in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1522) in
              FStar_Errors.log_issue rng uu____1517
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en ->
    fun t ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1 in
        let uu____1545 = FStar_Syntax_Util.head_and_args t2 in
        match uu____1545 with
        | (head, args) ->
            let uu____1590 =
              let uu____1605 =
                let uu____1606 = FStar_Syntax_Util.un_uinst head in
                uu____1606.FStar_Syntax_Syntax.n in
              (uu____1605, args) in
            (match uu____1590 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1622) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____1644::(hd, uu____1646)::(tl, uu____1648)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1715 = pat_terms hd in
                 let uu____1718 = pat_terms tl in
                 FStar_List.append uu____1715 uu____1718
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____1722::(pat, uu____1724)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (subpats, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1809 -> []) in
      let rec aux t1 =
        let uu____1834 =
          let uu____1835 = FStar_Syntax_Subst.compress t1 in
          uu____1835.FStar_Syntax_Syntax.n in
        match uu____1834 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1840 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1841 -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1842 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1843 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1844 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1857 -> []
        | FStar_Syntax_Syntax.Tm_unknown -> []
        | FStar_Syntax_Syntax.Tm_abs uu____1858 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1877 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1892 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1899 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1922 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1935 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____1950 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____1958 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid in
            if uu____1958 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2, args) ->
            let uu____1988 = aux t2 in
            FStar_List.fold_left
              (fun acc ->
                 fun uu____2005 ->
                   match uu____2005 with
                   | (t3, uu____2017) ->
                       let uu____2022 = aux t3 in
                       FStar_List.append acc uu____2022) uu____1988 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2026, uu____2027) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2, uu____2069) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2, uu____2075) -> aux t2 in
      let tlist =
        let uu____2083 = FStar_All.pipe_right t pat_terms in
        FStar_All.pipe_right uu____2083 (FStar_List.collect aux) in
      if (FStar_List.length tlist) = Prims.int_zero
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s ->
                fun t1 ->
                  let uu____2099 =
                    let uu____2100 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat " " uu____2100 in
                  Prims.op_Hat s uu____2099) "" tlist in
         let uu____2101 =
           let uu____2106 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2106) in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2101)
let check_smt_pat :
  'uuuuuu2117 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu2117) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env ->
    fun t ->
      fun bs ->
        fun c ->
          let uu____2158 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____2158
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2159;
                  FStar_Syntax_Syntax.effect_name = uu____2160;
                  FStar_Syntax_Syntax.result_typ = uu____2161;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats, uu____2165)::[];
                  FStar_Syntax_Syntax.flags = uu____2166;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2228 -> failwith "Impossible"
          else ()
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun env ->
    fun actuals ->
      fun expected_c ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env in
            let env1 =
              let uu___396_2292 = env in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___396_2292.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___396_2292.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___396_2292.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___396_2292.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___396_2292.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___396_2292.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___396_2292.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___396_2292.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___396_2292.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___396_2292.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___396_2292.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___396_2292.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___396_2292.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___396_2292.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___396_2292.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___396_2292.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.use_eq_strict =
                  (uu___396_2292.FStar_TypeChecker_Env.use_eq_strict);
                FStar_TypeChecker_Env.is_iface =
                  (uu___396_2292.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___396_2292.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___396_2292.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___396_2292.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___396_2292.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___396_2292.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___396_2292.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___396_2292.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___396_2292.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___396_2292.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___396_2292.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___396_2292.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___396_2292.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___396_2292.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___396_2292.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___396_2292.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___396_2292.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___396_2292.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.try_solve_implicits_hook =
                  (uu___396_2292.FStar_TypeChecker_Env.try_solve_implicits_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___396_2292.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.mpreprocess =
                  (uu___396_2292.FStar_TypeChecker_Env.mpreprocess);
                FStar_TypeChecker_Env.postprocess =
                  (uu___396_2292.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___396_2292.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___396_2292.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___396_2292.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___396_2292.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (uu___396_2292.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (uu___396_2292.FStar_TypeChecker_Env.erasable_types_tab);
                FStar_TypeChecker_Env.enable_defer_to_tac =
                  (uu___396_2292.FStar_TypeChecker_Env.enable_defer_to_tac)
              } in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid in
            let decreases_clause bs c =
              (let uu____2320 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
               if uu____2320
               then
                 let uu____2321 =
                   FStar_Syntax_Print.binders_to_string ", " bs in
                 let uu____2322 = FStar_Syntax_Print.comp_to_string c in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2321 uu____2322
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2353 ->
                         match uu____2353 with
                         | (b, uu____2363) ->
                             let t =
                               let uu____2369 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2369 in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2372 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2373 -> []
                              | uu____2388 ->
                                  let uu____2389 =
                                    FStar_Syntax_Syntax.bv_to_name b in
                                  [uu____2389]))) in
               let as_lex_list dec =
                 let uu____2402 = FStar_Syntax_Util.head_and_args dec in
                 match uu____2402 with
                 | (head, uu____2422) ->
                     (match head.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2450 -> mk_lex_list [dec]) in
               let cflags = FStar_Syntax_Util.comp_flags c in
               let uu____2458 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2467 ->
                         match uu___1_2467 with
                         | FStar_Syntax_Syntax.DECREASES uu____2468 -> true
                         | uu____2471 -> false)) in
               match uu____2458 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2477 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions in
                   mk_lex_list xs) in
            let previous_dec = decreases_clause actuals expected_c in
            let guard_one_letrec uu____2513 =
              match uu____2513 with
              | (l, arity, t, u_names) ->
                  let uu____2534 =
                    FStar_TypeChecker_Normalize.get_n_binders env1 arity t in
                  (match uu____2534 with
                   | (formals, c) ->
                       (if arity > (FStar_List.length formals)
                        then
                          failwith
                            "impossible: bad formals arity, guard_one_letrec"
                        else ();
                        (let formals1 =
                           FStar_All.pipe_right formals
                             (FStar_List.map
                                (fun uu____2599 ->
                                   match uu____2599 with
                                   | (x, imp) ->
                                       let uu____2618 =
                                         FStar_Syntax_Syntax.is_null_bv x in
                                       if uu____2618
                                       then
                                         let uu____2625 =
                                           let uu____2626 =
                                             let uu____2629 =
                                               FStar_Syntax_Syntax.range_of_bv
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____2629 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____2626
                                             x.FStar_Syntax_Syntax.sort in
                                         (uu____2625, imp)
                                       else (x, imp))) in
                         let dec = decreases_clause formals1 c in
                         let precedes1 =
                           let uu____2639 =
                             let uu____2640 = FStar_Syntax_Syntax.as_arg dec in
                             let uu____2649 =
                               let uu____2660 =
                                 FStar_Syntax_Syntax.as_arg previous_dec in
                               [uu____2660] in
                             uu____2640 :: uu____2649 in
                           FStar_Syntax_Syntax.mk_Tm_app precedes uu____2639
                             r in
                         let precedes2 =
                           FStar_TypeChecker_Util.label
                             "Could not prove termination of this recursive call"
                             r precedes1 in
                         let uu____2694 = FStar_Util.prefix formals1 in
                         match uu____2694 with
                         | (bs, (last, imp)) ->
                             let last1 =
                               let uu___459_2757 = last in
                               let uu____2758 =
                                 FStar_Syntax_Util.refine last precedes2 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___459_2757.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___459_2757.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____2758
                               } in
                             let refined_formals =
                               FStar_List.append bs [(last1, imp)] in
                             let t' =
                               FStar_Syntax_Util.arrow refined_formals c in
                             ((let uu____2794 =
                                 FStar_TypeChecker_Env.debug env1
                                   FStar_Options.Medium in
                               if uu____2794
                               then
                                 let uu____2795 =
                                   FStar_Syntax_Print.lbname_to_string l in
                                 let uu____2796 =
                                   FStar_Syntax_Print.term_to_string t in
                                 let uu____2797 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print3
                                   "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                   uu____2795 uu____2796 uu____2797
                               else ());
                              (l, t', u_names))))) in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
let (wrap_guard_with_tactic_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun topt ->
    fun g ->
      match topt with
      | FStar_Pervasives_Native.None -> g
      | FStar_Pervasives_Native.Some tactic ->
          FStar_TypeChecker_Env.always_map_guard g
            (fun g1 ->
               let uu____2853 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1 in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2853)
let (is_comp_ascribed_reflect :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu____2875 =
      let uu____2876 = FStar_Syntax_Subst.compress e in
      uu____2876.FStar_Syntax_Syntax.n in
    match uu____2875 with
    | FStar_Syntax_Syntax.Tm_ascribed
        (e1, (FStar_Util.Inr uu____2888, uu____2889), uu____2890) ->
        let uu____2937 =
          let uu____2938 = FStar_Syntax_Subst.compress e1 in
          uu____2938.FStar_Syntax_Syntax.n in
        (match uu____2937 with
         | FStar_Syntax_Syntax.Tm_app (head, args) when
             (FStar_List.length args) = Prims.int_one ->
             let uu____2983 =
               let uu____2984 = FStar_Syntax_Subst.compress head in
               uu____2984.FStar_Syntax_Syntax.n in
             (match uu____2983 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect l)
                  ->
                  let uu____2996 =
                    let uu____3003 = FStar_All.pipe_right args FStar_List.hd in
                    FStar_All.pipe_right uu____3003
                      (fun uu____3059 ->
                         match uu____3059 with
                         | (e2, aqual) -> (l, e2, aqual)) in
                  FStar_All.pipe_right uu____2996
                    (fun uu____3112 ->
                       FStar_Pervasives_Native.Some uu____3112)
              | uu____3113 -> FStar_Pervasives_Native.None)
         | uu____3120 -> FStar_Pervasives_Native.None)
    | uu____3127 -> FStar_Pervasives_Native.None
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      (let uu____3842 = FStar_TypeChecker_Env.debug env FStar_Options.Medium in
       if uu____3842
       then
         let uu____3843 =
           let uu____3844 = FStar_TypeChecker_Env.get_range env in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3844 in
         let uu____3845 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1 in
         let uu____3846 = FStar_Syntax_Print.term_to_string e in
         let uu____3847 =
           let uu____3848 = FStar_Syntax_Subst.compress e in
           FStar_Syntax_Print.tag_of_term uu____3848 in
         let uu____3849 =
           let uu____3850 = FStar_TypeChecker_Env.expected_typ env in
           match uu____3850 with
           | FStar_Pervasives_Native.None -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____3843 uu____3845 uu____3846 uu____3847 uu____3849
       else ());
      (let uu____3855 =
         FStar_Util.record_time
           (fun uu____3873 ->
              tc_maybe_toplevel_term
                (let uu___502_3876 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___502_3876.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___502_3876.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___502_3876.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___502_3876.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___502_3876.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___502_3876.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___502_3876.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___502_3876.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___502_3876.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___502_3876.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___502_3876.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___502_3876.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___502_3876.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___502_3876.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___502_3876.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___502_3876.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___502_3876.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___502_3876.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___502_3876.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___502_3876.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___502_3876.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___502_3876.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___502_3876.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___502_3876.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___502_3876.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___502_3876.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___502_3876.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___502_3876.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___502_3876.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___502_3876.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___502_3876.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___502_3876.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___502_3876.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___502_3876.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___502_3876.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___502_3876.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___502_3876.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___502_3876.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___502_3876.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___502_3876.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___502_3876.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___502_3876.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___502_3876.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___502_3876.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___502_3876.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___502_3876.FStar_TypeChecker_Env.enable_defer_to_tac)
                 }) e) in
       match uu____3855 with
       | (r, ms) ->
           ((let uu____3898 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____3898
             then
               ((let uu____3900 =
                   let uu____3901 = FStar_TypeChecker_Env.get_range env in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3901 in
                 let uu____3902 = FStar_Syntax_Print.term_to_string e in
                 let uu____3903 =
                   let uu____3904 = FStar_Syntax_Subst.compress e in
                   FStar_Syntax_Print.tag_of_term uu____3904 in
                 let uu____3905 = FStar_Util.string_of_int ms in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3900 uu____3902 uu____3903 uu____3905);
                (let uu____3906 = r in
                 match uu____3906 with
                 | (e1, lc, uu____3915) ->
                     let uu____3916 =
                       let uu____3917 = FStar_TypeChecker_Env.get_range env in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3917 in
                     let uu____3918 = FStar_Syntax_Print.term_to_string e1 in
                     let uu____3919 =
                       FStar_TypeChecker_Common.lcomp_to_string lc in
                     let uu____3920 =
                       let uu____3921 = FStar_Syntax_Subst.compress e1 in
                       FStar_Syntax_Print.tag_of_term uu____3921 in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____3916 uu____3918 uu____3919 uu____3920))
             else ());
            r))
and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      (let uu____3935 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
       if uu____3935
       then
         let uu____3936 =
           let uu____3937 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3937 in
         let uu____3938 = FStar_Syntax_Print.tag_of_term top in
         let uu____3939 = FStar_Syntax_Print.term_to_string top in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3936 uu____3938
           uu____3939
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3947 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3968 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3975 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3988 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3989 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3990 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3991 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3992 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4011 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4026 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4033 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt, qi) ->
           let projl uu___2_4049 =
             match uu___2_4049 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4055 -> failwith "projl fail" in
           let non_trivial_antiquotes qi1 =
             let is_name t =
               let uu____4068 =
                 let uu____4069 = FStar_Syntax_Subst.compress t in
                 uu____4069.FStar_Syntax_Syntax.n in
               match uu____4068 with
               | FStar_Syntax_Syntax.Tm_name uu____4072 -> true
               | uu____4073 -> false in
             FStar_Util.for_some
               (fun uu____4082 ->
                  match uu____4082 with
                  | (uu____4087, t) ->
                      let uu____4089 = is_name t in
                      Prims.op_Negation uu____4089)
               qi1.FStar_Syntax_Syntax.antiquotes in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static when non_trivial_antiquotes qi
                ->
                let e0 = e in
                let newbvs =
                  FStar_List.map
                    (fun uu____4107 ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs in
                let lbs =
                  FStar_List.map
                    (fun uu____4150 ->
                       match uu____4150 with
                       | ((bv, t), bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z in
                let qi1 =
                  let uu___575_4179 = qi in
                  let uu____4180 =
                    FStar_List.map
                      (fun uu____4208 ->
                         match uu____4208 with
                         | ((bv, uu____4224), bv') ->
                             let uu____4236 =
                               FStar_Syntax_Syntax.bv_to_name bv' in
                             (bv, uu____4236)) z in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___575_4179.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4180
                  } in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    top.FStar_Syntax_Syntax.pos in
                let e1 =
                  FStar_List.fold_left
                    (fun t ->
                       fun lb ->
                         let uu____4248 =
                           let uu____4249 =
                             let uu____4262 =
                               let uu____4265 =
                                 let uu____4266 =
                                   let uu____4273 =
                                     projl lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Syntax_Syntax.mk_binder uu____4273 in
                                 [uu____4266] in
                               FStar_Syntax_Subst.close uu____4265 t in
                             ((false, [lb]), uu____4262) in
                           FStar_Syntax_Syntax.Tm_let uu____4249 in
                         FStar_Syntax_Syntax.mk uu____4248
                           top.FStar_Syntax_Syntax.pos) nq lbs in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term in
                let uu____4306 =
                  FStar_List.fold_right
                    (fun uu____4342 ->
                       fun uu____4343 ->
                         match (uu____4342, uu____4343) with
                         | ((bv, tm), (aqs_rev, guard)) ->
                             let uu____4412 = tc_term env_tm tm in
                             (match uu____4412 with
                              | (tm1, uu____4430, g) ->
                                  let uu____4432 =
                                    FStar_TypeChecker_Env.conj_guard g guard in
                                  (((bv, tm1) :: aqs_rev), uu____4432))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard) in
                (match uu____4306 with
                 | (aqs_rev, guard) ->
                     let qi1 =
                       let uu___603_4474 = qi in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___603_4474.FStar_Syntax_Syntax.qkind);
                         FStar_Syntax_Syntax.antiquotes =
                           (FStar_List.rev aqs_rev)
                       } in
                     let tm =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                         top.FStar_Syntax_Syntax.pos in
                     value_check_expected_typ env1 tm
                       (FStar_Util.Inl FStar_Syntax_Syntax.t_term) guard)
            | FStar_Syntax_Syntax.Quote_dynamic ->
                let c = FStar_Syntax_Syntax.mk_Tac FStar_Syntax_Syntax.t_term in
                let uu____4485 =
                  FStar_TypeChecker_Env.clear_expected_typ env1 in
                (match uu____4485 with
                 | (env', uu____4499) ->
                     let uu____4504 =
                       tc_term
                         (let uu___612_4513 = env' in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___612_4513.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___612_4513.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___612_4513.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___612_4513.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___612_4513.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___612_4513.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___612_4513.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___612_4513.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___612_4513.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___612_4513.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___612_4513.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___612_4513.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___612_4513.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___612_4513.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___612_4513.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___612_4513.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___612_4513.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___612_4513.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___612_4513.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___612_4513.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___612_4513.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___612_4513.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___612_4513.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___612_4513.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___612_4513.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___612_4513.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___612_4513.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___612_4513.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___612_4513.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___612_4513.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___612_4513.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___612_4513.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___612_4513.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___612_4513.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___612_4513.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___612_4513.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___612_4513.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___612_4513.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___612_4513.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___612_4513.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___612_4513.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___612_4513.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___612_4513.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___612_4513.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___612_4513.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___612_4513.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) qt in
                     (match uu____4504 with
                      | (qt1, uu____4521, uu____4522) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4528 =
                            let uu____4535 =
                              let uu____4540 =
                                FStar_TypeChecker_Common.lcomp_of_comp c in
                              FStar_Util.Inr uu____4540 in
                            value_check_expected_typ env1 top uu____4535
                              FStar_TypeChecker_Env.trivial_guard in
                          (match uu____4528 with
                           | (t1, lc, g) ->
                               let t2 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (t1,
                                        (FStar_Syntax_Syntax.Meta_monadic_lift
                                           (FStar_Parser_Const.effect_PURE_lid,
                                             FStar_Parser_Const.effect_TAC_lid,
                                             FStar_Syntax_Syntax.t_term))))
                                   t1.FStar_Syntax_Syntax.pos in
                               (t2, lc, g)))))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____4557;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4558;
             FStar_Syntax_Syntax.ltyp = uu____4559;
             FStar_Syntax_Syntax.rng = uu____4560;_}
           ->
           let uu____4571 = FStar_Syntax_Util.unlazy top in
           tc_term env1 uu____4571
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat))
           ->
           let uu____4578 = tc_tot_or_gtot_term env1 e1 in
           (match uu____4578 with
            | (e2, c, g) ->
                let g1 =
                  let uu___642_4595 = g in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___642_4595.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___642_4595.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___642_4595.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___642_4595.FStar_TypeChecker_Common.implicits)
                  } in
                let uu____4596 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    top.FStar_Syntax_Syntax.pos in
                (uu____4596, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_pattern (names, pats)) ->
           let uu____4638 = FStar_Syntax_Util.type_u () in
           (match uu____4638 with
            | (t, u) ->
                let uu____4651 = tc_check_tot_or_gtot_term env1 e1 t "" in
                (match uu____4651 with
                 | (e2, c, g) ->
                     let uu____4667 =
                       let uu____4684 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____4684 with
                       | (env2, uu____4708) -> tc_smt_pats env2 pats in
                     (match uu____4667 with
                      | (pats1, g') ->
                          let g'1 =
                            let uu___665_4746 = g' in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred_to_tac =
                                (uu___665_4746.FStar_TypeChecker_Common.deferred_to_tac);
                              FStar_TypeChecker_Common.deferred =
                                (uu___665_4746.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___665_4746.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___665_4746.FStar_TypeChecker_Common.implicits)
                            } in
                          let uu____4747 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names, pats1))))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4766 =
                            FStar_TypeChecker_Env.conj_guard g g'1 in
                          (uu____4747, c, uu____4766))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence))
           ->
           let uu____4772 =
             let uu____4773 = FStar_Syntax_Subst.compress e1 in
             uu____4773.FStar_Syntax_Syntax.n in
           (match uu____4772 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4782,
                  { FStar_Syntax_Syntax.lbname = x;
                    FStar_Syntax_Syntax.lbunivs = uu____4784;
                    FStar_Syntax_Syntax.lbtyp = uu____4785;
                    FStar_Syntax_Syntax.lbeff = uu____4786;
                    FStar_Syntax_Syntax.lbdef = e11;
                    FStar_Syntax_Syntax.lbattrs = uu____4788;
                    FStar_Syntax_Syntax.lbpos = uu____4789;_}::[]),
                 e2)
                ->
                let uu____4817 =
                  let uu____4824 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____4824 e11 in
                (match uu____4817 with
                 | (e12, c1, g1) ->
                     let uu____4834 = tc_term env1 e2 in
                     (match uu____4834 with
                      | (e21, c2, g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2) in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c2.FStar_TypeChecker_Common.res_typ in
                          let attrs =
                            let uu____4858 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name in
                            if uu____4858
                            then [FStar_Syntax_Util.inline_let_attr]
                            else [] in
                          let e3 =
                            let uu____4865 =
                              let uu____4866 =
                                let uu____4879 =
                                  let uu____4886 =
                                    let uu____4889 =
                                      FStar_Syntax_Syntax.mk_lb
                                        (x, [],
                                          (c.FStar_TypeChecker_Common.eff_name),
                                          FStar_Syntax_Syntax.t_unit, e13,
                                          attrs,
                                          (e13.FStar_Syntax_Syntax.pos)) in
                                    [uu____4889] in
                                  (false, uu____4886) in
                                (uu____4879, e22) in
                              FStar_Syntax_Syntax.Tm_let uu____4866 in
                            FStar_Syntax_Syntax.mk uu____4865
                              e1.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.res_typ in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4910 =
                            FStar_TypeChecker_Env.conj_guard g1 g2 in
                          (e5, c, uu____4910)))
            | uu____4911 ->
                let uu____4912 = tc_term env1 e1 in
                (match uu____4912 with
                 | (e2, c, g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         top.FStar_Syntax_Syntax.pos in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_monadic uu____4934) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_monadic_lift uu____4946) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1, m) ->
           let uu____4965 = tc_term env1 e1 in
           (match uu____4965 with
            | (e2, c, g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____4986, (FStar_Util.Inr expected_c, _tacopt), uu____4989)
           when
           let uu____5036 = FStar_All.pipe_right top is_comp_ascribed_reflect in
           FStar_All.pipe_right uu____5036 FStar_Util.is_some ->
           let uu____5067 =
             let uu____5078 =
               FStar_All.pipe_right top is_comp_ascribed_reflect in
             FStar_All.pipe_right uu____5078 FStar_Util.must in
           (match uu____5067 with
            | (effect_lid, e1, aqual) ->
                let uu____5152 =
                  FStar_TypeChecker_Env.clear_expected_typ env1 in
                (match uu____5152 with
                 | (env0, uu____5166) ->
                     let uu____5171 = tc_comp env0 expected_c in
                     (match uu____5171 with
                      | (expected_c1, uu____5185, g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1 in
                          ((let uu____5189 =
                              let uu____5190 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name in
                              Prims.op_Negation uu____5190 in
                            if uu____5189
                            then
                              let uu____5191 =
                                let uu____5196 =
                                  let uu____5197 =
                                    FStar_Ident.string_of_lid effect_lid in
                                  let uu____5198 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5197 uu____5198 in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5196) in
                              FStar_Errors.raise_error uu____5191
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5201 =
                              let uu____5202 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid in
                              Prims.op_Negation uu____5202 in
                            if uu____5201
                            then
                              let uu____5203 =
                                let uu____5208 =
                                  let uu____5209 =
                                    FStar_Ident.string_of_lid effect_lid in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5209 in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5208) in
                              FStar_Errors.raise_error uu____5203
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd in
                            let repr =
                              let uu____5215 =
                                let uu____5218 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5218 u_c in
                              FStar_All.pipe_right uu____5215 FStar_Util.must in
                            let e2 =
                              let uu____5224 =
                                let uu____5225 =
                                  let uu____5252 =
                                    let uu____5269 =
                                      let uu____5278 =
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          (FStar_Pervasives_Native.Some u_c) in
                                      FStar_Util.Inr uu____5278 in
                                    (uu____5269,
                                      FStar_Pervasives_Native.None) in
                                  (e1, uu____5252,
                                    FStar_Pervasives_Native.None) in
                                FStar_Syntax_Syntax.Tm_ascribed uu____5225 in
                              FStar_Syntax_Syntax.mk uu____5224
                                e1.FStar_Syntax_Syntax.pos in
                            (let uu____5320 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme in
                             if uu____5320
                             then
                               let uu____5321 =
                                 FStar_Syntax_Print.term_to_string e2 in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5321
                             else ());
                            (let uu____5323 = tc_tot_or_gtot_term env0 e2 in
                             match uu____5323 with
                             | (e3, uu____5337, g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3 in
                                 ((let uu____5341 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme in
                                   if uu____5341
                                   then
                                     let uu____5342 =
                                       FStar_Syntax_Print.term_to_string e4 in
                                     let uu____5343 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5342 uu____5343
                                   else ());
                                  (let top1 =
                                     let r = top.FStar_Syntax_Syntax.pos in
                                     let tm =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_reflect
                                               effect_lid)) r in
                                     let tm1 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (tm, [(e4, aqual)])) r in
                                     let uu____5387 =
                                       let uu____5388 =
                                         let uu____5415 =
                                           let uu____5418 =
                                             FStar_All.pipe_right expected_c1
                                               FStar_Syntax_Util.comp_effect_name in
                                           FStar_All.pipe_right uu____5418
                                             (fun uu____5423 ->
                                                FStar_Pervasives_Native.Some
                                                  uu____5423) in
                                         (tm1,
                                           ((FStar_Util.Inr expected_c1),
                                             _tacopt), uu____5415) in
                                       FStar_Syntax_Syntax.Tm_ascribed
                                         uu____5388 in
                                     FStar_Syntax_Syntax.mk uu____5387 r in
                                   let uu____5460 =
                                     let uu____5467 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     comp_check_expected_typ env1 top1
                                       uu____5467 in
                                   match uu____5460 with
                                   | (top2, c, g_env) ->
                                       let uu____5477 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env] in
                                       (top2, c, uu____5477)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inr expected_c, topt), uu____5481) ->
           let uu____5528 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____5528 with
            | (env0, uu____5542) ->
                let uu____5547 = tc_comp env0 expected_c in
                (match uu____5547 with
                 | (expected_c1, uu____5561, g) ->
                     let uu____5563 =
                       let uu____5570 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0) in
                       tc_term uu____5570 e1 in
                     (match uu____5563 with
                      | (e2, c', g') ->
                          let uu____5580 =
                            let uu____5591 =
                              FStar_TypeChecker_Common.lcomp_comp c' in
                            match uu____5591 with
                            | (c'1, g_c') ->
                                let uu____5608 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1) in
                                (match uu____5608 with
                                 | (e3, expected_c2, g'') ->
                                     let uu____5628 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g'' in
                                     (e3, expected_c2, uu____5628)) in
                          (match uu____5580 with
                           | (e3, expected_c2, g'') ->
                               let uu____5650 = tc_tactic_opt env0 topt in
                               (match uu____5650 with
                                | (topt1, gtac) ->
                                    let e4 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_ascribed
                                           (e3,
                                             ((FStar_Util.Inr expected_c2),
                                               topt1),
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.comp_effect_name
                                                   expected_c2))))
                                        top.FStar_Syntax_Syntax.pos in
                                    let lc =
                                      FStar_TypeChecker_Common.lcomp_of_comp
                                        expected_c2 in
                                    let f =
                                      let uu____5710 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g'' in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____5710 in
                                    let uu____5711 =
                                      comp_check_expected_typ env1 e4 lc in
                                    (match uu____5711 with
                                     | (e5, c, f2) ->
                                         let final_guard =
                                           let uu____5728 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2 in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____5728 in
                                         let uu____5729 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac in
                                         (e5, c, uu____5729)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inl t, topt), uu____5733) ->
           let uu____5780 = FStar_Syntax_Util.type_u () in
           (match uu____5780 with
            | (k, u) ->
                let uu____5793 = tc_check_tot_or_gtot_term env1 t k "" in
                (match uu____5793 with
                 | (t1, uu____5807, f) ->
                     let uu____5809 = tc_tactic_opt env1 topt in
                     (match uu____5809 with
                      | (topt1, gtac) ->
                          let uu____5828 =
                            let uu____5835 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                            tc_term uu____5835 e1 in
                          (match uu____5828 with
                           | (e2, c, g) ->
                               let uu____5845 =
                                 let uu____5850 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____5855 ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____5850 e2 c f in
                               (match uu____5845 with
                                | (c1, f1) ->
                                    let uu____5864 =
                                      let uu____5871 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_TypeChecker_Common.eff_name))))
                                          top.FStar_Syntax_Syntax.pos in
                                      comp_check_expected_typ env1 uu____5871
                                        c1 in
                                    (match uu____5864 with
                                     | (e3, c2, f2) ->
                                         let final_guard =
                                           let uu____5918 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2 in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____5918 in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard in
                                         let uu____5920 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac in
                                         (e3, c2, uu____5920)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____5921;
              FStar_Syntax_Syntax.vars = uu____5922;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6001 = FStar_Syntax_Util.head_and_args top in
           (match uu____6001 with
            | (unary_op, uu____6025) ->
                let head =
                  let uu____6053 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6053 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____6101;
              FStar_Syntax_Syntax.vars = uu____6102;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6181 = FStar_Syntax_Util.head_and_args top in
           (match uu____6181 with
            | (unary_op, uu____6205) ->
                let head =
                  let uu____6233 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6233 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6281);
              FStar_Syntax_Syntax.pos = uu____6282;
              FStar_Syntax_Syntax.vars = uu____6283;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6362 = FStar_Syntax_Util.head_and_args top in
           (match uu____6362 with
            | (unary_op, uu____6386) ->
                let head =
                  let uu____6414 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6414 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____6462;
              FStar_Syntax_Syntax.vars = uu____6463;_},
            a1::a2::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6559 = FStar_Syntax_Util.head_and_args top in
           (match uu____6559 with
            | (unary_op, uu____6583) ->
                let head =
                  let uu____6611 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    uu____6611 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____6667;
              FStar_Syntax_Syntax.vars = uu____6668;_},
            (e1, FStar_Pervasives_Native.None)::[])
           ->
           let uu____6706 =
             let uu____6713 =
               let uu____6714 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6714 in
             tc_term uu____6713 e1 in
           (match uu____6706 with
            | (e2, c, g) ->
                let uu____6738 = FStar_Syntax_Util.head_and_args top in
                (match uu____6738 with
                 | (head, uu____6762) ->
                     let uu____6787 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head, [(e2, FStar_Pervasives_Native.None)]))
                         top.FStar_Syntax_Syntax.pos in
                     let uu____6820 =
                       let uu____6821 =
                         let uu____6822 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____6822 in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____6821 in
                     (uu____6787, uu____6820, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____6823;
              FStar_Syntax_Syntax.vars = uu____6824;_},
            (t, FStar_Pervasives_Native.None)::(r,
                                                FStar_Pervasives_Native.None)::[])
           ->
           let uu____6877 = FStar_Syntax_Util.head_and_args top in
           (match uu____6877 with
            | (head, uu____6901) ->
                let env' =
                  let uu____6927 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____6927 in
                let uu____6928 = tc_term env' r in
                (match uu____6928 with
                 | (er, uu____6942, gr) ->
                     let uu____6944 = tc_term env1 t in
                     (match uu____6944 with
                      | (t1, tt, gt) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt in
                          let uu____6961 =
                            let uu____6962 =
                              let uu____6963 = FStar_Syntax_Syntax.as_arg t1 in
                              let uu____6972 =
                                let uu____6983 = FStar_Syntax_Syntax.as_arg r in
                                [uu____6983] in
                              uu____6963 :: uu____6972 in
                            FStar_Syntax_Syntax.mk_Tm_app head uu____6962
                              top.FStar_Syntax_Syntax.pos in
                          (uu____6961, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____7016;
              FStar_Syntax_Syntax.vars = uu____7017;_},
            uu____7018)
           ->
           let uu____7043 =
             let uu____7048 =
               let uu____7049 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____7049 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7048) in
           FStar_Errors.raise_error uu____7043 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____7056;
              FStar_Syntax_Syntax.vars = uu____7057;_},
            uu____7058)
           ->
           let uu____7083 =
             let uu____7088 =
               let uu____7089 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____7089 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7088) in
           FStar_Errors.raise_error uu____7083 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____7096;
              FStar_Syntax_Syntax.vars = uu____7097;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7140 = FStar_TypeChecker_Env.clear_expected_typ env1 in
             match uu____7140 with
             | (env0, uu____7154) ->
                 let uu____7159 = tc_term env0 e1 in
                 (match uu____7159 with
                  | (e2, c, g) ->
                      let uu____7175 = FStar_Syntax_Util.head_and_args top in
                      (match uu____7175 with
                       | (reify_op, uu____7199) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ in
                           let uu____7225 =
                             FStar_TypeChecker_Common.lcomp_comp c in
                           (match uu____7225 with
                            | (c1, g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1 in
                                ((let uu____7240 =
                                    let uu____7241 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef in
                                    Prims.op_Negation uu____7241 in
                                  if uu____7240
                                  then
                                    let uu____7242 =
                                      let uu____7247 =
                                        let uu____7248 =
                                          FStar_Ident.string_of_lid ef in
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          uu____7248 in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7247) in
                                    FStar_Errors.raise_error uu____7242
                                      e2.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let repr =
                                    FStar_TypeChecker_Env.reify_comp env1 c1
                                      u_c in
                                  let e3 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (reify_op, [(e2, aqual)]))
                                      top.FStar_Syntax_Syntax.pos in
                                  let c2 =
                                    let uu____7287 =
                                      FStar_TypeChecker_Env.is_total_effect
                                        env1 ef in
                                    if uu____7287
                                    then
                                      let uu____7288 =
                                        FStar_Syntax_Syntax.mk_Total repr in
                                      FStar_All.pipe_right uu____7288
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
                                         } in
                                       let uu____7299 =
                                         FStar_Syntax_Syntax.mk_Comp ct in
                                       FStar_All.pipe_right uu____7299
                                         FStar_TypeChecker_Common.lcomp_of_comp) in
                                  let uu____7300 =
                                    comp_check_expected_typ env1 e3 c2 in
                                  match uu____7300 with
                                  | (e4, c3, g') ->
                                      let uu____7316 =
                                        let uu____7317 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g' in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7317 in
                                      (e4, c3, uu____7316))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7319;
              FStar_Syntax_Syntax.vars = uu____7320;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7364 =
               let uu____7365 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l in
               Prims.op_Negation uu____7365 in
             if uu____7364
             then
               let uu____7366 =
                 let uu____7371 =
                   let uu____7372 = FStar_Ident.string_of_lid l in
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     uu____7372 in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7371) in
               FStar_Errors.raise_error uu____7366 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7374 = FStar_Syntax_Util.head_and_args top in
             match uu____7374 with
             | (reflect_op, uu____7398) ->
                 let uu____7423 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____7423 with
                  | FStar_Pervasives_Native.None ->
                      let uu____7444 =
                        let uu____7449 =
                          let uu____7450 = FStar_Ident.string_of_lid l in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7450 in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7449) in
                      FStar_Errors.raise_error uu____7444
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                      let uu____7469 =
                        FStar_TypeChecker_Env.clear_expected_typ env1 in
                      (match uu____7469 with
                       | (env_no_ex, uu____7483) ->
                           let uu____7488 =
                             let uu____7497 =
                               tc_tot_or_gtot_term env_no_ex e1 in
                             match uu____7497 with
                             | (e2, c, g) ->
                                 ((let uu____7516 =
                                     let uu____7517 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7517 in
                                   if uu____7516
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g)) in
                           (match uu____7488 with
                            | (e2, c_e, g_e) ->
                                let uu____7546 =
                                  let uu____7561 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____7561 with
                                  | (a, u_a) ->
                                      let uu____7582 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a in
                                      (match uu____7582 with
                                       | (a_uvar, uu____7610, g_a) ->
                                           let uu____7624 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar in
                                           (uu____7624, u_a, a_uvar, g_a)) in
                                (match uu____7546 with
                                 | ((expected_repr_typ, g_repr), u_a, a, g_a)
                                     ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ in
                                     let eff_args =
                                       let uu____7666 =
                                         let uu____7667 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ in
                                         uu____7667.FStar_Syntax_Syntax.n in
                                       match uu____7666 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7680, uu____7681::args) ->
                                           args
                                       | uu____7723 ->
                                           let uu____7724 =
                                             let uu____7729 =
                                               let uu____7730 =
                                                 FStar_Ident.string_of_lid l in
                                               let uu____7731 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ in
                                               let uu____7732 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____7730 uu____7731
                                                 uu____7732 in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____7729) in
                                           FStar_Errors.raise_error
                                             uu____7724
                                             top.FStar_Syntax_Syntax.pos in
                                     let c =
                                       let uu____7744 =
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
                                           } in
                                       FStar_All.pipe_right uu____7744
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         top.FStar_Syntax_Syntax.pos in
                                     let uu____7780 =
                                       comp_check_expected_typ env1 e3 c in
                                     (match uu____7780 with
                                      | (e4, c1, g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_TypeChecker_Common.eff_name),
                                                        (c1.FStar_TypeChecker_Common.res_typ)))))
                                              e4.FStar_Syntax_Syntax.pos in
                                          let uu____7803 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g'] in
                                          (e5, c1, uu____7803))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head, (tau, FStar_Pervasives_Native.None)::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7842 = FStar_Syntax_Util.head_and_args top in
           (match uu____7842 with
            | (head1, args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head,
            (uu____7892, FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____7893))::(tau,
                                                          FStar_Pervasives_Native.None)::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7945 = FStar_Syntax_Util.head_and_args top in
           (match uu____7945 with
            | (head1, args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head, args) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8020 =
             match args with
             | (tau, FStar_Pervasives_Native.None)::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau, FStar_Pervasives_Native.None)::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8229 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos in
           (match uu____8020 with
            | (args1, args2) ->
                let t1 = FStar_Syntax_Util.mk_app head args1 in
                let t2 = FStar_Syntax_Util.mk_app t1 args2 in tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head, args) ->
           let env0 = env1 in
           let env2 =
             let uu____8346 =
               let uu____8347 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____8347 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____8346 instantiate_both in
           ((let uu____8363 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____8363
             then
               let uu____8364 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____8365 = FStar_Syntax_Print.term_to_string top in
               let uu____8366 =
                 let uu____8367 = FStar_TypeChecker_Env.expected_typ env0 in
                 FStar_All.pipe_right uu____8367
                   (fun uu___3_8373 ->
                      match uu___3_8373 with
                      | FStar_Pervasives_Native.None -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t) in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8364
                 uu____8365 uu____8366
             else ());
            (let uu____8378 = tc_term (no_inst env2) head in
             match uu____8378 with
             | (head1, chead, g_head) ->
                 let uu____8394 =
                   let uu____8399 = FStar_TypeChecker_Common.lcomp_comp chead in
                   FStar_All.pipe_right uu____8399
                     (fun uu____8416 ->
                        match uu____8416 with
                        | (c, g) ->
                            let uu____8427 =
                              FStar_TypeChecker_Env.conj_guard g_head g in
                            (c, uu____8427)) in
                 (match uu____8394 with
                  | (chead1, g_head1) ->
                      let uu____8436 =
                        let uu____8443 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8445 = FStar_Options.lax () in
                              Prims.op_Negation uu____8445))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head1) in
                        if uu____8443
                        then
                          let uu____8452 =
                            let uu____8459 =
                              FStar_TypeChecker_Env.expected_typ env0 in
                            check_short_circuit_args env2 head1 chead1
                              g_head1 args uu____8459 in
                          match uu____8452 with | (e1, c, g) -> (e1, c, g)
                        else
                          (let uu____8472 =
                             FStar_TypeChecker_Env.expected_typ env0 in
                           check_application_args env2 head1 chead1 g_head1
                             args uu____8472) in
                      (match uu____8436 with
                       | (e1, c, g) ->
                           let uu____8484 =
                             let uu____8491 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c in
                             if uu____8491
                             then
                               FStar_TypeChecker_Util.maybe_instantiate env0
                                 e1 c
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard) in
                           (match uu____8484 with
                            | (e2, c1, implicits) ->
                                ((let uu____8509 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme in
                                  if uu____8509
                                  then
                                    let uu____8510 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8510
                                  else ());
                                 (let uu____8512 =
                                    comp_check_expected_typ env0 e2 c1 in
                                  match uu____8512 with
                                  | (e3, c2, g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits in
                                      ((let uu____8531 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme in
                                        if uu____8531
                                        then
                                          let uu____8532 =
                                            FStar_Syntax_Print.term_to_string
                                              e3 in
                                          let uu____8533 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1 in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8532 uu____8533
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8535 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8558;
               FStar_Syntax_Syntax.lbunivs = uu____8559;
               FStar_Syntax_Syntax.lbtyp = uu____8560;
               FStar_Syntax_Syntax.lbeff = uu____8561;
               FStar_Syntax_Syntax.lbdef = uu____8562;
               FStar_Syntax_Syntax.lbattrs = uu____8563;
               FStar_Syntax_Syntax.lbpos = uu____8564;_}::[]),
            uu____8565)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false, uu____8588), uu____8589) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8604;
               FStar_Syntax_Syntax.lbunivs = uu____8605;
               FStar_Syntax_Syntax.lbtyp = uu____8606;
               FStar_Syntax_Syntax.lbeff = uu____8607;
               FStar_Syntax_Syntax.lbdef = uu____8608;
               FStar_Syntax_Syntax.lbattrs = uu____8609;
               FStar_Syntax_Syntax.lbpos = uu____8610;_}::uu____8611),
            uu____8612)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true, uu____8637), uu____8638) ->
           check_inner_let_rec env1 top)
and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      let uu____8661 =
        let uu____8662 = FStar_Syntax_Subst.compress top in
        uu____8662.FStar_Syntax_Syntax.n in
      match uu____8661 with
      | FStar_Syntax_Syntax.Tm_match (e1, eqns) ->
          let uu____8709 = FStar_TypeChecker_Env.clear_expected_typ env in
          (match uu____8709 with
           | (env1, topt) ->
               let env11 = instantiate_both env1 in
               let uu____8729 = tc_term env11 e1 in
               (match uu____8729 with
                | (e11, c1, g1) ->
                    let uu____8745 =
                      let uu____8756 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1 in
                      match uu____8756 with
                      | FStar_Pervasives_Native.Some (e12, c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None -> (e11, c1, eqns) in
                    (match uu____8745 with
                     | (e12, c11, eqns1) ->
                         let eqns2 = eqns1 in
                         let uu____8811 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None ->
                               let uu____8825 = FStar_Syntax_Util.type_u () in
                               (match uu____8825 with
                                | (k, uu____8837) ->
                                    let uu____8838 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k in
                                    (match uu____8838 with
                                     | (res_t, uu____8858, g) ->
                                         let uu____8872 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t in
                                         let uu____8873 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g in
                                         (uu____8872, res_t, uu____8873))) in
                         (match uu____8811 with
                          | (env_branches, res_t, g11) ->
                              ((let uu____8884 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme in
                                if uu____8884
                                then
                                  let uu____8885 =
                                    FStar_Syntax_Print.term_to_string res_t in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____8885
                                else ());
                               (let guard_x =
                                  FStar_Syntax_Syntax.new_bv
                                    (FStar_Pervasives_Native.Some
                                       (e12.FStar_Syntax_Syntax.pos))
                                    c11.FStar_TypeChecker_Common.res_typ in
                                let t_eqns =
                                  FStar_All.pipe_right eqns2
                                    (FStar_List.map
                                       (tc_eqn guard_x env_branches)) in
                                let uu____8984 =
                                  let uu____8991 =
                                    FStar_List.fold_right
                                      (fun uu____9078 ->
                                         fun uu____9079 ->
                                           match (uu____9078, uu____9079)
                                           with
                                           | ((branch, f, eff_label, cflags,
                                               c, g, erasable_branch),
                                              (caccum, gaccum, erasable)) ->
                                               let uu____9329 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9329,
                                                 (erasable || erasable_branch)))
                                      t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false) in
                                  match uu____8991 with
                                  | (cases, g, erasable) ->
                                      let uu____9430 =
                                        FStar_TypeChecker_Util.bind_cases env
                                          res_t cases guard_x in
                                      (uu____9430, g, erasable) in
                                match uu____8984 with
                                | (c_branches, g_branches, erasable) ->
                                    let cres =
                                      FStar_TypeChecker_Util.bind
                                        e12.FStar_Syntax_Syntax.pos env
                                        (FStar_Pervasives_Native.Some e12)
                                        c11
                                        ((FStar_Pervasives_Native.Some
                                            guard_x), c_branches) in
                                    let cres1 =
                                      if erasable
                                      then
                                        let e =
                                          FStar_Syntax_Util.exp_true_bool in
                                        let c =
                                          FStar_Syntax_Syntax.mk_GTotal'
                                            FStar_Syntax_Util.t_bool
                                            (FStar_Pervasives_Native.Some
                                               FStar_Syntax_Syntax.U_zero) in
                                        let uu____9446 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9446
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____9583 ->
                                                  match uu____9583 with
                                                  | ((pat, wopt, br),
                                                     uu____9629, eff_label,
                                                     uu____9631, uu____9632,
                                                     uu____9633, uu____9634)
                                                      ->
                                                      let uu____9669 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t in
                                                      (pat, wopt, uu____9669))) in
                                        let e =
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_match
                                               (scrutinee, branches))
                                            top.FStar_Syntax_Syntax.pos in
                                        let e2 =
                                          FStar_TypeChecker_Util.maybe_monadic
                                            env e
                                            cres1.FStar_TypeChecker_Common.eff_name
                                            cres1.FStar_TypeChecker_Common.res_typ in
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl
                                                   (cres1.FStar_TypeChecker_Common.res_typ)),
                                                 FStar_Pervasives_Native.None),
                                               (FStar_Pervasives_Native.Some
                                                  (cres1.FStar_TypeChecker_Common.eff_name))))
                                          e2.FStar_Syntax_Syntax.pos in
                                      let uu____9736 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name in
                                      if uu____9736
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____9741 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x in
                                           mk_match uu____9741 in
                                         let lb =
                                           let uu____9745 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____9745 e12 []
                                             e12.FStar_Syntax_Syntax.pos in
                                         let e =
                                           let uu____9751 =
                                             let uu____9752 =
                                               let uu____9765 =
                                                 let uu____9768 =
                                                   let uu____9769 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       guard_x in
                                                   [uu____9769] in
                                                 FStar_Syntax_Subst.close
                                                   uu____9768 e_match in
                                               ((false, [lb]), uu____9765) in
                                             FStar_Syntax_Syntax.Tm_let
                                               uu____9752 in
                                           FStar_Syntax_Syntax.mk uu____9751
                                             top.FStar_Syntax_Syntax.pos in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ) in
                                    ((let uu____9799 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme in
                                      if uu____9799
                                      then
                                        let uu____9800 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos in
                                        let uu____9801 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1 in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____9800 uu____9801
                                      else ());
                                     (let uu____9803 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches in
                                      (e, cres1, uu____9803)))))))))
      | uu____9804 ->
          let uu____9805 =
            let uu____9806 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format1 "tc_match called on %s\n" uu____9806 in
          failwith uu____9805
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
  fun head ->
    fun env ->
      fun args ->
        fun rng ->
          let uu____9829 =
            match args with
            | (tau, FStar_Pervasives_Native.None)::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9868))::(tau, FStar_Pervasives_Native.None)::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9908 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng in
          match uu____9829 with
          | (tau, atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None ->
                    let uu____9939 = FStar_TypeChecker_Env.expected_typ env in
                    (match uu____9939 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None ->
                         let uu____9943 = FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9943) in
              let uu____9944 =
                let uu____9951 =
                  let uu____9952 =
                    let uu____9953 = FStar_Syntax_Util.type_u () in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9953 in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9952 in
                tc_term uu____9951 typ in
              (match uu____9944 with
               | (typ1, uu____9969, g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9972 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau in
                     match uu____9972 with
                     | (tau1, uu____9986, g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1338_9991 = tau1 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1338_9991.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1338_9991.FStar_Syntax_Syntax.vars)
                                }) in
                           (let uu____9993 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac") in
                            if uu____9993
                            then
                              let uu____9994 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print1 "Got %s\n" uu____9994
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____9997 =
                              let uu____9998 =
                                FStar_Syntax_Syntax.mk_Total typ1 in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____9998 in
                            (t, uu____9997,
                              FStar_TypeChecker_Env.trivial_guard)))))))
and (tc_tactic :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun a ->
    fun b ->
      fun env ->
        fun tau ->
          let env1 =
            let uu___1348_10004 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1348_10004.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1348_10004.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1348_10004.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1348_10004.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1348_10004.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1348_10004.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1348_10004.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1348_10004.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1348_10004.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1348_10004.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1348_10004.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1348_10004.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1348_10004.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1348_10004.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1348_10004.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1348_10004.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1348_10004.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1348_10004.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1348_10004.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1348_10004.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1348_10004.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1348_10004.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1348_10004.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1348_10004.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1348_10004.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1348_10004.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1348_10004.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1348_10004.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1348_10004.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1348_10004.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1348_10004.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1348_10004.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1348_10004.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1348_10004.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1348_10004.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1348_10004.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1348_10004.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1348_10004.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1348_10004.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1348_10004.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1348_10004.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1348_10004.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1348_10004.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1348_10004.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1348_10004.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___1348_10004.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let uu____10005 = FStar_Syntax_Syntax.t_tac_of a b in
          tc_check_tot_or_gtot_term env1 tau uu____10005 ""
and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun topt ->
      match topt with
      | FStar_Pervasives_Native.None ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____10027 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic in
          (match uu____10027 with
           | (tactic1, uu____10041, g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))
and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      let check_instantiated_fvar env1 v dc e1 t0 =
        let t = FStar_Syntax_Util.remove_inacc t0 in
        let uu____10094 =
          let uu____10101 =
            let uu____10102 = FStar_Syntax_Syntax.mk_Total t in
            FStar_All.pipe_right uu____10102
              FStar_TypeChecker_Common.lcomp_of_comp in
          FStar_TypeChecker_Util.maybe_instantiate env1 e1 uu____10101 in
        match uu____10094 with
        | (e2, lc, implicits) ->
            let is_data_ctor uu___4_10119 =
              match uu___4_10119 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10122) -> true
              | uu____10129 -> false in
            let uu____10132 =
              (is_data_ctor dc) &&
                (let uu____10134 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____10134) in
            if uu____10132
            then
              let uu____10141 =
                let uu____10146 =
                  let uu____10147 =
                    FStar_Ident.string_of_lid v.FStar_Syntax_Syntax.v in
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    uu____10147 in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10146) in
              let uu____10148 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____10141 uu____10148
            else
              value_check_expected_typ env1 e2 (FStar_Util.Inr lc) implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10165 =
            let uu____10170 =
              let uu____10171 = FStar_Syntax_Print.term_to_string top in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10171 in
            (FStar_Errors.Error_IllScopedTerm, uu____10170) in
          FStar_Errors.raise_error uu____10165 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____10196 =
            let uu____10201 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
            FStar_Util.Inl uu____10201 in
          value_check_expected_typ env1 e uu____10196
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____10203 =
            let uu____10216 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____10216 with
            | FStar_Pervasives_Native.None ->
                let uu____10231 = FStar_Syntax_Util.type_u () in
                (match uu____10231 with
                 | (k, u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard) in
          (match uu____10203 with
           | (t, uu____10268, g0) ->
               let uu____10282 =
                 let uu____10295 =
                   let uu____10296 = FStar_Range.string_of_range r in
                   Prims.op_Hat "user-provided implicit term at " uu____10296 in
                 FStar_TypeChecker_Util.new_implicit_var uu____10295 r env1 t in
               (match uu____10282 with
                | (e1, uu____10304, g1) ->
                    let uu____10318 =
                      let uu____10319 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____10319
                        FStar_TypeChecker_Common.lcomp_of_comp in
                    let uu____10320 = FStar_TypeChecker_Env.conj_guard g0 g1 in
                    (e1, uu____10318, uu____10320)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10322 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10331 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____10331)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____10322 with
           | (t, rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1412_10344 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1412_10344.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1412_10344.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____10347 =
                   let uu____10354 =
                     let uu____10355 = FStar_Syntax_Syntax.mk_Total t in
                     FStar_All.pipe_right uu____10355
                       FStar_TypeChecker_Common.lcomp_of_comp in
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1
                     uu____10354 in
                 match uu____10347 with
                 | (e2, c, implicits) ->
                     value_check_expected_typ env1 e2 (FStar_Util.Inr c)
                       implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10366;
             FStar_Syntax_Syntax.vars = uu____10367;_},
           uu____10368)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10373 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10373
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10381 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10381
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10389;
             FStar_Syntax_Syntax.vars = uu____10390;_},
           us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____10399 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10399 with
           | ((us', t), range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range in
               (maybe_warn_on_use env1 fv1;
                if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10424 =
                     let uu____10429 =
                       let uu____10430 = FStar_Syntax_Print.fv_to_string fv1 in
                       let uu____10431 =
                         FStar_Util.string_of_int (FStar_List.length us1) in
                       let uu____10432 =
                         FStar_Util.string_of_int (FStar_List.length us') in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10430 uu____10431 uu____10432 in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10429) in
                   let uu____10433 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____10424 uu____10433)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10451 -> failwith "Impossible") us' us1;
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____10454 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____10454 us1 in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_uinst (uu____10455, us) ->
          let uu____10461 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
              "Universe applications are only allowed on top-level identifiers")
            uu____10461
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10469 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10469 with
           | ((us, t), range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range in
               (maybe_warn_on_use env1 fv1;
                (let uu____10494 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____10494
                 then
                   let uu____10495 =
                     let uu____10496 = FStar_Syntax_Syntax.lid_of_fv fv1 in
                     FStar_Syntax_Print.lid_to_string uu____10496 in
                   let uu____10497 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____10498 = FStar_Range.string_of_range range in
                   let uu____10499 = FStar_Range.string_of_use_range range in
                   let uu____10500 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____10495 uu____10497 uu____10498 uu____10499
                     uu____10500
                 else ());
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____10504 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____10504 us in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____10532 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10532 with
           | (bs1, c1) ->
               let env0 = env1 in
               let uu____10546 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____10546 with
                | (env2, uu____10560) ->
                    let uu____10565 = tc_binders env2 bs1 in
                    (match uu____10565 with
                     | (bs2, env3, g, us) ->
                         let uu____10584 = tc_comp env3 c1 in
                         (match uu____10584 with
                          | (c2, uc, f) ->
                              let e1 =
                                let uu___1496_10603 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1496_10603.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1496_10603.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____10614 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____10614 in
                                let g2 =
                                  FStar_TypeChecker_Util.close_guard_implicits
                                    env3 false bs2 g1 in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g2))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              top.FStar_Syntax_Syntax.pos in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              top.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu____10630 =
            let uu____10635 =
              let uu____10636 = FStar_Syntax_Syntax.mk_binder x in
              [uu____10636] in
            FStar_Syntax_Subst.open_term uu____10635 phi in
          (match uu____10630 with
           | (x1, phi1) ->
               let env0 = env1 in
               let uu____10664 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____10664 with
                | (env2, uu____10678) ->
                    let uu____10683 =
                      let uu____10698 = FStar_List.hd x1 in
                      tc_binder env2 uu____10698 in
                    (match uu____10683 with
                     | (x2, env3, f1, u) ->
                         ((let uu____10734 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____10734
                           then
                             let uu____10735 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____10736 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____10737 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10735 uu____10736 uu____10737
                           else ());
                          (let uu____10741 = FStar_Syntax_Util.type_u () in
                           match uu____10741 with
                           | (t_phi, uu____10753) ->
                               let uu____10754 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                   "refinement formula must be pure or ghost" in
                               (match uu____10754 with
                                | (phi2, uu____10768, f2) ->
                                    let e1 =
                                      let uu___1534_10773 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1534_10773.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1534_10773.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____10782 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10782 in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____10810) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____10837 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
            if uu____10837
            then
              let uu____10838 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1547_10841 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1547_10841.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1547_10841.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10838
            else ());
           (let uu____10855 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____10855 with
            | (bs2, body1) -> tc_abs env1 top bs2 body1))
      | uu____10868 ->
          let uu____10869 =
            let uu____10870 = FStar_Syntax_Print.term_to_string top in
            let uu____10871 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10870
              uu____10871 in
          failwith uu____10869
and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun r ->
      fun c ->
        let res =
          match c with
          | FStar_Const.Const_unit -> FStar_Syntax_Syntax.t_unit
          | FStar_Const.Const_bool uu____10882 -> FStar_Syntax_Util.t_bool
          | FStar_Const.Const_int (uu____10883, FStar_Pervasives_Native.None)
              -> FStar_Syntax_Syntax.t_int
          | FStar_Const.Const_int
              (uu____10894, FStar_Pervasives_Native.Some msize) ->
              FStar_Syntax_Syntax.tconst
                (match msize with
                 | (FStar_Const.Signed, FStar_Const.Int8) ->
                     FStar_Parser_Const.int8_lid
                 | (FStar_Const.Signed, FStar_Const.Int16) ->
                     FStar_Parser_Const.int16_lid
                 | (FStar_Const.Signed, FStar_Const.Int32) ->
                     FStar_Parser_Const.int32_lid
                 | (FStar_Const.Signed, FStar_Const.Int64) ->
                     FStar_Parser_Const.int64_lid
                 | (FStar_Const.Unsigned, FStar_Const.Int8) ->
                     FStar_Parser_Const.uint8_lid
                 | (FStar_Const.Unsigned, FStar_Const.Int16) ->
                     FStar_Parser_Const.uint16_lid
                 | (FStar_Const.Unsigned, FStar_Const.Int32) ->
                     FStar_Parser_Const.uint32_lid
                 | (FStar_Const.Unsigned, FStar_Const.Int64) ->
                     FStar_Parser_Const.uint64_lid)
          | FStar_Const.Const_string uu____10910 ->
              FStar_Syntax_Syntax.t_string
          | FStar_Const.Const_real uu____10915 -> FStar_Syntax_Syntax.t_real
          | FStar_Const.Const_float uu____10916 ->
              FStar_Syntax_Syntax.t_float
          | FStar_Const.Const_char uu____10917 ->
              let uu____10918 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
              FStar_All.pipe_right uu____10918 FStar_Util.must
          | FStar_Const.Const_effect -> FStar_Syntax_Util.ktype0
          | FStar_Const.Const_range uu____10923 ->
              FStar_Syntax_Syntax.t_range
          | FStar_Const.Const_range_of ->
              let uu____10924 =
                let uu____10929 =
                  let uu____10930 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____10930 in
                (FStar_Errors.Fatal_IllTyped, uu____10929) in
              FStar_Errors.raise_error uu____10924 r
          | FStar_Const.Const_set_range_of ->
              let uu____10931 =
                let uu____10936 =
                  let uu____10937 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____10937 in
                (FStar_Errors.Fatal_IllTyped, uu____10936) in
              FStar_Errors.raise_error uu____10931 r
          | FStar_Const.Const_reify ->
              let uu____10938 =
                let uu____10943 =
                  let uu____10944 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____10944 in
                (FStar_Errors.Fatal_IllTyped, uu____10943) in
              FStar_Errors.raise_error uu____10938 r
          | FStar_Const.Const_reflect uu____10945 ->
              let uu____10946 =
                let uu____10951 =
                  let uu____10952 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____10952 in
                (FStar_Errors.Fatal_IllTyped, uu____10951) in
              FStar_Errors.raise_error uu____10946 r
          | uu____10953 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnsupportedConstant,
                  "Unsupported constant") r in
        FStar_Syntax_Subst.set_use_range r res
and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c ->
      let c0 = c in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t, uu____10970) ->
          let uu____10979 = FStar_Syntax_Util.type_u () in
          (match uu____10979 with
           | (k, u) ->
               let uu____10992 = tc_check_tot_or_gtot_term env t k "" in
               (match uu____10992 with
                | (t1, uu____11006, g) ->
                    let uu____11008 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____11008, u, g)))
      | FStar_Syntax_Syntax.GTotal (t, uu____11010) ->
          let uu____11019 = FStar_Syntax_Util.type_u () in
          (match uu____11019 with
           | (k, u) ->
               let uu____11032 = tc_check_tot_or_gtot_term env t k "" in
               (match uu____11032 with
                | (t1, uu____11046, g) ->
                    let uu____11048 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____11048, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          let head1 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head, us))
                  c0.FStar_Syntax_Syntax.pos in
          let tc =
            let uu____11056 =
              let uu____11057 =
                FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ in
              uu____11057 :: (c1.FStar_Syntax_Syntax.effect_args) in
            FStar_Syntax_Syntax.mk_Tm_app head1 uu____11056
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____11074 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff "" in
          (match uu____11074 with
           | (tc1, uu____11088, f) ->
               let uu____11090 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____11090 with
                | (head2, args) ->
                    let comp_univs =
                      let uu____11140 =
                        let uu____11141 = FStar_Syntax_Subst.compress head2 in
                        uu____11141.FStar_Syntax_Syntax.n in
                      match uu____11140 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11144, us) -> us
                      | uu____11150 -> [] in
                    let uu____11151 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____11151 with
                     | (uu____11174, args1) ->
                         let uu____11200 =
                           let uu____11223 = FStar_List.hd args1 in
                           let uu____11240 = FStar_List.tl args1 in
                           (uu____11223, uu____11240) in
                         (match uu____11200 with
                          | (res, args2) ->
                              let uu____11321 =
                                let uu____11330 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_11358 ->
                                          match uu___5_11358 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____11366 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____11366 with
                                               | (env1, uu____11378) ->
                                                   let uu____11383 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____11383 with
                                                    | (e1, uu____11395, g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard))) in
                                FStar_All.pipe_right uu____11330
                                  FStar_List.unzip in
                              (match uu____11321 with
                               | (flags, guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1677_11436 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1677_11436.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags = flags
                                        }) in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u) in
                                   let uu____11442 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards in
                                   (c2, u_c, uu____11442))))))
and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____11452 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____11453 -> u2
        | FStar_Syntax_Syntax.U_zero -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____11465 = aux u3 in
            FStar_Syntax_Syntax.U_succ uu____11465
        | FStar_Syntax_Syntax.U_max us ->
            let uu____11469 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____11469
        | FStar_Syntax_Syntax.U_name x ->
            let uu____11473 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x) in
            if uu____11473
            then u2
            else
              (let uu____11475 =
                 let uu____11476 =
                   let uu____11477 = FStar_Syntax_Print.univ_to_string u2 in
                   Prims.op_Hat uu____11477 " not found" in
                 Prims.op_Hat "Universe variable " uu____11476 in
               failwith uu____11475) in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown ->
             let uu____11479 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____11479 FStar_Pervasives_Native.snd
         | uu____11488 -> aux u)
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
  fun env ->
    fun bs ->
      fun t0 ->
        fun body ->
          match t0 with
          | FStar_Pervasives_Native.None ->
              ((match env.FStar_TypeChecker_Env.letrecs with
                | [] -> ()
                | uu____11522 ->
                    failwith
                      "Impossible: Can't have a let rec annotation but no expected type");
               (let uu____11533 = tc_binders env bs in
                match uu____11533 with
                | (bs1, envbody, g_env, uu____11563) ->
                    (FStar_Pervasives_Native.None, bs1, [],
                      FStar_Pervasives_Native.None, envbody, body, g_env)))
          | FStar_Pervasives_Native.Some t ->
              let t1 = FStar_Syntax_Subst.compress t in
              let rec as_function_typ norm1 t2 =
                let uu____11607 =
                  let uu____11608 = FStar_Syntax_Subst.compress t2 in
                  uu____11608.FStar_Syntax_Syntax.n in
                match uu____11607 with
                | FStar_Syntax_Syntax.Tm_uvar uu____11631 ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____11653 -> failwith "Impossible");
                     (let uu____11664 = tc_binders env bs in
                      match uu____11664 with
                      | (bs1, envbody, g_env, uu____11696) ->
                          let uu____11697 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody in
                          (match uu____11697 with
                           | (envbody1, uu____11725) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____11736;
                       FStar_Syntax_Syntax.pos = uu____11737;
                       FStar_Syntax_Syntax.vars = uu____11738;_},
                     uu____11739)
                    ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____11785 -> failwith "Impossible");
                     (let uu____11796 = tc_binders env bs in
                      match uu____11796 with
                      | (bs1, envbody, g_env, uu____11828) ->
                          let uu____11829 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody in
                          (match uu____11829 with
                           | (envbody1, uu____11857) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_refine (b, uu____11869) ->
                    let uu____11874 =
                      as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                    (match uu____11874 with
                     | (uu____11915, bs1, bs', copt, env_body, body1, g_env)
                         ->
                         ((FStar_Pervasives_Native.Some t2), bs1, bs', copt,
                           env_body, body1, g_env))
                | FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) ->
                    let uu____11962 =
                      FStar_Syntax_Subst.open_comp bs_expected c_expected in
                    (match uu____11962 with
                     | (bs_expected1, c_expected1) ->
                         let check_actuals_against_formals env1 bs1
                           bs_expected2 body1 =
                           let rec handle_more uu____12097 c_expected2 body2
                             =
                             match uu____12097 with
                             | (env_bs, bs2, more, guard_env, subst) ->
                                 (match more with
                                  | FStar_Pervasives_Native.None ->
                                      let uu____12211 =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2 in
                                      (env_bs, bs2, guard_env, uu____12211,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inr more_bs_expected) ->
                                      let c =
                                        let uu____12228 =
                                          FStar_Syntax_Util.arrow
                                            more_bs_expected c_expected2 in
                                        FStar_Syntax_Syntax.mk_Total
                                          uu____12228 in
                                      let uu____12229 =
                                        FStar_Syntax_Subst.subst_comp subst c in
                                      (env_bs, bs2, guard_env, uu____12229,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inl more_bs) ->
                                      let c =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2 in
                                      let uu____12246 =
                                        (FStar_Options.ml_ish ()) ||
                                          (FStar_Syntax_Util.is_named_tot c) in
                                      if uu____12246
                                      then
                                        let t3 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env_bs
                                            (FStar_Syntax_Util.comp_result c) in
                                        (match t3.FStar_Syntax_Syntax.n with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs_expected3, c_expected3) ->
                                             let uu____12310 =
                                               FStar_Syntax_Subst.open_comp
                                                 bs_expected3 c_expected3 in
                                             (match uu____12310 with
                                              | (bs_expected4, c_expected4)
                                                  ->
                                                  let uu____12337 =
                                                    tc_abs_check_binders
                                                      env_bs more_bs
                                                      bs_expected4 in
                                                  (match uu____12337 with
                                                   | (env_bs_bs', bs', more1,
                                                      guard'_env_bs, subst1)
                                                       ->
                                                       let guard'_env =
                                                         FStar_TypeChecker_Env.close_guard
                                                           env_bs bs2
                                                           guard'_env_bs in
                                                       let uu____12392 =
                                                         let uu____12419 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard_env
                                                             guard'_env in
                                                         (env_bs_bs',
                                                           (FStar_List.append
                                                              bs2 bs'),
                                                           more1,
                                                           uu____12419,
                                                           subst1) in
                                                       handle_more
                                                         uu____12392
                                                         c_expected4 body2))
                                         | uu____12442 ->
                                             let body3 =
                                               FStar_Syntax_Util.abs more_bs
                                                 body2
                                                 FStar_Pervasives_Native.None in
                                             (env_bs, bs2, guard_env, c,
                                               body3))
                                      else
                                        (let body3 =
                                           FStar_Syntax_Util.abs more_bs
                                             body2
                                             FStar_Pervasives_Native.None in
                                         (env_bs, bs2, guard_env, c, body3))) in
                           let uu____12470 =
                             tc_abs_check_binders env1 bs1 bs_expected2 in
                           handle_more uu____12470 c_expected1 body1 in
                         let mk_letrec_env envbody bs1 c =
                           let letrecs = guard_letrecs envbody bs1 c in
                           let envbody1 =
                             let uu___1808_12535 = envbody in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1808_12535.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1808_12535.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1808_12535.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1808_12535.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1808_12535.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1808_12535.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1808_12535.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1808_12535.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1808_12535.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1808_12535.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1808_12535.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1808_12535.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1808_12535.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs = [];
                               FStar_TypeChecker_Env.top_level =
                                 (uu___1808_12535.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1808_12535.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___1808_12535.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (uu___1808_12535.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1808_12535.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1808_12535.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1808_12535.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1808_12535.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1808_12535.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1808_12535.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1808_12535.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1808_12535.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1808_12535.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1808_12535.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1808_12535.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1808_12535.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1808_12535.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1808_12535.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1808_12535.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1808_12535.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1808_12535.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1808_12535.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1808_12535.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1808_12535.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1808_12535.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1808_12535.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1808_12535.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1808_12535.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1808_12535.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1808_12535.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1808_12535.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1808_12535.FStar_TypeChecker_Env.erasable_types_tab);
                               FStar_TypeChecker_Env.enable_defer_to_tac =
                                 (uu___1808_12535.FStar_TypeChecker_Env.enable_defer_to_tac)
                             } in
                           let uu____12544 =
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____12610 ->
                                     fun uu____12611 ->
                                       match (uu____12610, uu____12611) with
                                       | ((env1, letrec_binders, g),
                                          (l, t3, u_names)) ->
                                           let uu____12702 =
                                             let uu____12709 =
                                               let uu____12710 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env1 in
                                               FStar_All.pipe_right
                                                 uu____12710
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____12709 t3 in
                                           (match uu____12702 with
                                            | (t4, uu____12734, g') ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env1 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____12747 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___1826_12750
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___1826_12750.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___1826_12750.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____12747 ::
                                                        letrec_binders
                                                  | uu____12751 ->
                                                      letrec_binders in
                                                let uu____12756 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g' in
                                                (env2, lb, uu____12756)))
                                  (envbody1, [],
                                    FStar_TypeChecker_Env.trivial_guard)) in
                           match uu____12544 with
                           | (envbody2, letrec_binders, g) ->
                               let uu____12776 =
                                 FStar_TypeChecker_Env.close_guard envbody2
                                   bs1 g in
                               (envbody2, letrec_binders, uu____12776) in
                         let envbody =
                           let uu___1834_12780 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1834_12780.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1834_12780.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1834_12780.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1834_12780.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1834_12780.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1834_12780.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1834_12780.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1834_12780.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1834_12780.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1834_12780.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1834_12780.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1834_12780.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1834_12780.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs = [];
                             FStar_TypeChecker_Env.top_level =
                               (uu___1834_12780.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1834_12780.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1834_12780.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1834_12780.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1834_12780.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1834_12780.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___1834_12780.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1834_12780.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1834_12780.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1834_12780.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1834_12780.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1834_12780.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1834_12780.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1834_12780.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1834_12780.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1834_12780.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1834_12780.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1834_12780.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1834_12780.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1834_12780.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1834_12780.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1834_12780.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1834_12780.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1834_12780.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1834_12780.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1834_12780.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1834_12780.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1834_12780.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1834_12780.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1834_12780.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1834_12780.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1834_12780.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1834_12780.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let uu____12789 =
                           check_actuals_against_formals envbody bs
                             bs_expected1 body in
                         (match uu____12789 with
                          | (envbody1, bs1, g_env, c, body1) ->
                              let envbody2 =
                                let uu___1843_12826 = envbody1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1843_12826.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1843_12826.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1843_12826.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___1843_12826.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1843_12826.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___1843_12826.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1843_12826.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1843_12826.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1843_12826.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1843_12826.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1843_12826.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1843_12826.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1843_12826.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (env.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1843_12826.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1843_12826.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1843_12826.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1843_12826.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1843_12826.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1843_12826.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1843_12826.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1843_12826.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1843_12826.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1843_12826.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1843_12826.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1843_12826.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1843_12826.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1843_12826.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1843_12826.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1843_12826.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1843_12826.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1843_12826.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1843_12826.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1843_12826.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1843_12826.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1843_12826.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1843_12826.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1843_12826.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1843_12826.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1843_12826.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1843_12826.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1843_12826.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1843_12826.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1843_12826.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1843_12826.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1843_12826.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1843_12826.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____12827 = mk_letrec_env envbody2 bs1 c in
                              (match uu____12827 with
                               | (envbody3, letrecs, g_annots) ->
                                   let envbody4 =
                                     FStar_TypeChecker_Env.set_expected_typ
                                       envbody3
                                       (FStar_Syntax_Util.comp_result c) in
                                   let uu____12864 =
                                     FStar_TypeChecker_Env.conj_guard g_env
                                       g_annots in
                                   ((FStar_Pervasives_Native.Some t2), bs1,
                                     letrecs,
                                     (FStar_Pervasives_Native.Some c),
                                     envbody4, body1, uu____12864))))
                | uu____12871 ->
                    if Prims.op_Negation norm1
                    then
                      let uu____12892 =
                        let uu____12893 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.unfold_whnf env) in
                        FStar_All.pipe_right uu____12893
                          FStar_Syntax_Util.unascribe in
                      as_function_typ true uu____12892
                    else
                      (let uu____12895 =
                         tc_abs_expected_function_typ env bs
                           FStar_Pervasives_Native.None body in
                       match uu____12895 with
                       | (uu____12934, bs1, uu____12936, c_opt, envbody,
                          body1, g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, [],
                             c_opt, envbody, body1, g_env)) in
              as_function_typ false t1
and (tc_abs_check_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.binders *
          (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.binders)
          FStar_Util.either FStar_Pervasives_Native.option *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.subst_t))
  =
  fun env ->
    fun bs ->
      fun bs_expected ->
        let rec aux uu____13009 bs1 bs_expected1 =
          match uu____13009 with
          | (env1, subst) ->
              (match (bs1, bs_expected1) with
               | ([], []) ->
                   (env1, [], FStar_Pervasives_Native.None,
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ((uu____13116, FStar_Pervasives_Native.None)::uu____13117,
                  (hd_e, q)::uu____13120) when
                   FStar_Syntax_Syntax.is_implicit_or_meta q ->
                   let bv =
                     let uu____13172 =
                       let uu____13175 =
                         FStar_Ident.range_of_id
                           hd_e.FStar_Syntax_Syntax.ppname in
                       FStar_Pervasives_Native.Some uu____13175 in
                     let uu____13176 =
                       FStar_Syntax_Subst.subst subst
                         hd_e.FStar_Syntax_Syntax.sort in
                     FStar_Syntax_Syntax.new_bv uu____13172 uu____13176 in
                   aux (env1, subst) ((bv, q) :: bs1) bs_expected1
               | ((hd, imp)::bs2, (hd_expected, imp')::bs_expected2) ->
                   ((let special q1 q2 =
                       match (q1, q2) with
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13269),
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13270)) -> true
                       | (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Equality)) -> true
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____13279),
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13280)) -> true
                       | uu____13285 -> false in
                     let uu____13294 =
                       (Prims.op_Negation (special imp imp')) &&
                         (let uu____13296 =
                            FStar_Syntax_Util.eq_aqual imp imp' in
                          uu____13296 <> FStar_Syntax_Util.Equal) in
                     if uu____13294
                     then
                       let uu____13297 =
                         let uu____13302 =
                           let uu____13303 =
                             FStar_Syntax_Print.bv_to_string hd in
                           FStar_Util.format1
                             "Inconsistent implicit argument annotation on argument %s"
                             uu____13303 in
                         (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                           uu____13302) in
                       let uu____13304 = FStar_Syntax_Syntax.range_of_bv hd in
                       FStar_Errors.raise_error uu____13297 uu____13304
                     else ());
                    (let expected_t =
                       FStar_Syntax_Subst.subst subst
                         hd_expected.FStar_Syntax_Syntax.sort in
                     let uu____13307 =
                       let uu____13314 =
                         let uu____13315 =
                           FStar_Syntax_Util.unmeta
                             hd.FStar_Syntax_Syntax.sort in
                         uu____13315.FStar_Syntax_Syntax.n in
                       match uu____13314 with
                       | FStar_Syntax_Syntax.Tm_unknown ->
                           (expected_t, FStar_TypeChecker_Env.trivial_guard)
                       | uu____13326 ->
                           ((let uu____13328 =
                               FStar_TypeChecker_Env.debug env1
                                 FStar_Options.High in
                             if uu____13328
                             then
                               let uu____13329 =
                                 FStar_Syntax_Print.bv_to_string hd in
                               FStar_Util.print1 "Checking binder %s\n"
                                 uu____13329
                             else ());
                            (let uu____13331 =
                               tc_tot_or_gtot_term env1
                                 hd.FStar_Syntax_Syntax.sort in
                             match uu____13331 with
                             | (t, uu____13345, g1_env) ->
                                 let g2_env =
                                   let uu____13348 =
                                     FStar_TypeChecker_Rel.teq_nosmt env1 t
                                       expected_t in
                                   match uu____13348 with
                                   | FStar_Pervasives_Native.Some g ->
                                       FStar_All.pipe_right g
                                         (FStar_TypeChecker_Rel.resolve_implicits
                                            env1)
                                   | FStar_Pervasives_Native.None ->
                                       let uu____13352 =
                                         FStar_TypeChecker_Rel.get_subtyping_prop
                                           env1 expected_t t in
                                       (match uu____13352 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu____13355 =
                                              FStar_TypeChecker_Err.basic_type_error
                                                env1
                                                FStar_Pervasives_Native.None
                                                expected_t t in
                                            let uu____13360 =
                                              FStar_TypeChecker_Env.get_range
                                                env1 in
                                            FStar_Errors.raise_error
                                              uu____13355 uu____13360
                                        | FStar_Pervasives_Native.Some g_env
                                            ->
                                            FStar_TypeChecker_Util.label_guard
                                              (hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                              "Type annotation on parameter incompatible with the expected type"
                                              g_env) in
                                 let uu____13362 =
                                   FStar_TypeChecker_Env.conj_guard g1_env
                                     g2_env in
                                 (t, uu____13362))) in
                     match uu____13307 with
                     | (t, g_env) ->
                         let hd1 =
                           let uu___1939_13388 = hd in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1939_13388.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1939_13388.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t
                           } in
                         let b = (hd1, imp) in
                         let b_expected = (hd_expected, imp') in
                         let env_b = push_binding env1 b in
                         let subst1 =
                           let uu____13411 =
                             FStar_Syntax_Syntax.bv_to_name hd1 in
                           maybe_extend_subst subst b_expected uu____13411 in
                         let uu____13414 =
                           aux (env_b, subst1) bs2 bs_expected2 in
                         (match uu____13414 with
                          | (env_bs, bs3, rest, g'_env_b, subst2) ->
                              let g'_env =
                                FStar_TypeChecker_Env.close_guard env_bs 
                                  [b] g'_env_b in
                              let uu____13479 =
                                FStar_TypeChecker_Env.conj_guard g_env g'_env in
                              (env_bs, (b :: bs3), rest, uu____13479, subst2))))
               | (rest, []) ->
                   (env1, [],
                     (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ([], rest) ->
                   (env1, [],
                     (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                     FStar_TypeChecker_Env.trivial_guard, subst)) in
        aux (env, []) bs bs_expected
and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      fun bs ->
        fun body ->
          let fail msg t =
            let uu____13616 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top in
            FStar_Errors.raise_error uu____13616 top.FStar_Syntax_Syntax.pos in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____13622 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____13622 with
          | (env1, topt) ->
              ((let uu____13642 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____13642
                then
                  let uu____13643 =
                    match topt with
                    | FStar_Pervasives_Native.None -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13643
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13647 =
                  tc_abs_expected_function_typ env1 bs topt body in
                match uu____13647 with
                | (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1,
                   g_env) ->
                    ((let uu____13688 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme in
                      if uu____13688
                      then
                        let uu____13689 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t in
                        let uu____13691 =
                          match c_opt with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t in
                        let uu____13693 =
                          let uu____13694 =
                            FStar_TypeChecker_Env.expected_typ envbody in
                          match uu____13694 with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____13689 uu____13691 uu____13693
                      else ());
                     (let uu____13700 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC") in
                      if uu____13700
                      then
                        let uu____13701 =
                          FStar_Syntax_Print.binders_to_string ", " bs1 in
                        let uu____13702 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13701 uu____13702
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos in
                      let uu____13705 =
                        let uu____13716 =
                          let uu____13723 =
                            (FStar_All.pipe_right c_opt FStar_Util.is_some)
                              &&
                              (let uu____13731 =
                                 let uu____13732 =
                                   FStar_Syntax_Subst.compress body1 in
                                 uu____13732.FStar_Syntax_Syntax.n in
                               match uu____13731 with
                               | FStar_Syntax_Syntax.Tm_app (head, args) when
                                   (FStar_List.length args) = Prims.int_one
                                   ->
                                   let uu____13769 =
                                     let uu____13770 =
                                       FStar_Syntax_Subst.compress head in
                                     uu____13770.FStar_Syntax_Syntax.n in
                                   (match uu____13769 with
                                    | FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reflect
                                        uu____13773) -> true
                                    | uu____13774 -> false)
                               | uu____13775 -> false) in
                          if uu____13723
                          then
                            let uu____13782 =
                              let uu____13783 =
                                FStar_TypeChecker_Env.clear_expected_typ
                                  envbody1 in
                              FStar_All.pipe_right uu____13783
                                FStar_Pervasives_Native.fst in
                            let uu____13798 =
                              let uu____13799 =
                                let uu____13800 =
                                  let uu____13827 =
                                    let uu____13844 =
                                      let uu____13853 =
                                        FStar_All.pipe_right c_opt
                                          FStar_Util.must in
                                      FStar_Util.Inr uu____13853 in
                                    (uu____13844,
                                      FStar_Pervasives_Native.None) in
                                  (body1, uu____13827,
                                    FStar_Pervasives_Native.None) in
                                FStar_Syntax_Syntax.Tm_ascribed uu____13800 in
                              FStar_Syntax_Syntax.mk uu____13799
                                FStar_Range.dummyRange in
                            (uu____13782, uu____13798, false)
                          else
                            (let uu____13899 =
                               let uu____13900 =
                                 let uu____13907 =
                                   let uu____13908 =
                                     FStar_Syntax_Subst.compress body1 in
                                   uu____13908.FStar_Syntax_Syntax.n in
                                 (c_opt, uu____13907) in
                               match uu____13900 with
                               | (FStar_Pervasives_Native.None,
                                  FStar_Syntax_Syntax.Tm_ascribed
                                  (uu____13913,
                                   (FStar_Util.Inr expected_c, uu____13915),
                                   uu____13916)) -> false
                               | uu____13965 -> true in
                             (envbody1, body1, uu____13899)) in
                        match uu____13716 with
                        | (envbody2, body2, should_check_expected_effect) ->
                            let uu____13985 =
                              tc_term
                                (let uu___2024_13994 = envbody2 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2024_13994.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2024_13994.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2024_13994.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2024_13994.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2024_13994.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2024_13994.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2024_13994.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2024_13994.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2024_13994.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2024_13994.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2024_13994.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2024_13994.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2024_13994.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2024_13994.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level = false;
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2024_13994.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___2024_13994.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2024_13994.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2024_13994.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___2024_13994.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2024_13994.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2024_13994.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2024_13994.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2024_13994.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2024_13994.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2024_13994.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2024_13994.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2024_13994.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2024_13994.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2024_13994.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2024_13994.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2024_13994.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2024_13994.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2024_13994.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2024_13994.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___2024_13994.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2024_13994.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___2024_13994.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2024_13994.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2024_13994.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2024_13994.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2024_13994.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2024_13994.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___2024_13994.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___2024_13994.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___2024_13994.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) body2 in
                            (match uu____13985 with
                             | (body3, cbody, guard_body) ->
                                 let guard_body1 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     envbody2 guard_body in
                                 if should_check_expected_effect
                                 then
                                   let uu____14019 =
                                     FStar_TypeChecker_Common.lcomp_comp
                                       cbody in
                                   (match uu____14019 with
                                    | (cbody1, g_lc) ->
                                        let uu____14036 =
                                          check_expected_effect
                                            (let uu___2035_14045 = envbody2 in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 use_eq;
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.lax);
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.phase1);
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___2035_14045.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) c_opt (body3, cbody1) in
                                        (match uu____14036 with
                                         | (body4, cbody2, guard) ->
                                             let uu____14059 =
                                               let uu____14060 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_lc guard in
                                               FStar_TypeChecker_Env.conj_guard
                                                 guard_body1 uu____14060 in
                                             (body4, cbody2, uu____14059)))
                                 else
                                   (let uu____14066 =
                                      FStar_TypeChecker_Common.lcomp_comp
                                        cbody in
                                    match uu____14066 with
                                    | (cbody1, g_lc) ->
                                        let uu____14083 =
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 g_lc in
                                        (body3, cbody1, uu____14083))) in
                      match uu____13705 with
                      | (body2, cbody, guard_body) ->
                          let guard =
                            let uu____14106 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14108 =
                                   FStar_TypeChecker_Env.should_verify env1 in
                                 Prims.op_Negation uu____14108) in
                            if uu____14106
                            then
                              let uu____14109 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env in
                              let uu____14110 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body in
                              FStar_TypeChecker_Env.conj_guard uu____14109
                                uu____14110
                            else
                              (let guard =
                                 let uu____14113 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14113 in
                               guard) in
                          let guard1 =
                            FStar_TypeChecker_Util.close_guard_implicits env1
                              false bs1 guard in
                          let tfun_computed =
                            FStar_Syntax_Util.arrow bs1 cbody in
                          let e =
                            FStar_Syntax_Util.abs bs1 body2
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_comp_of_comp
                                    (FStar_Util.dflt cbody c_opt))) in
                          let uu____14127 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t in
                                let t_annot =
                                  match topt with
                                  | FStar_Pervasives_Native.Some t2 -> t2
                                  | FStar_Pervasives_Native.None ->
                                      failwith
                                        "Impossible! tc_abs: if tfun_computed is Some, expected topt to also be Some" in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____14150
                                     -> (e, t_annot, guard1)
                                 | uu____14165 ->
                                     let lc =
                                       let uu____14167 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed in
                                       FStar_All.pipe_right uu____14167
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     let uu____14168 =
                                       FStar_TypeChecker_Util.check_has_type
                                         env1 e lc t1 in
                                     (match uu____14168 with
                                      | (e1, uu____14182, guard') ->
                                          let uu____14184 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard' in
                                          (e1, t_annot, uu____14184)))
                            | FStar_Pervasives_Native.None ->
                                (e, tfun_computed, guard1) in
                          (match uu____14127 with
                           | (e1, tfun, guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun in
                               let uu____14195 =
                                 let uu____14200 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____14200 guard2 in
                               (match uu____14195 with
                                | (c1, g) -> (e1, c1, g)))))))
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
  fun env ->
    fun head ->
      fun chead ->
        fun ghead ->
          fun args ->
            fun expected_topt ->
              let n_args = FStar_List.length args in
              let r = FStar_TypeChecker_Env.get_range env in
              let thead = FStar_Syntax_Util.comp_result chead in
              (let uu____14250 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____14250
               then
                 let uu____14251 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos in
                 let uu____14252 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14251
                   uu____14252
               else ());
              (let monadic_application uu____14331 subst arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____14331 with
                 | (head1, chead1, ghead1, cres) ->
                     let uu____14400 =
                       check_no_escape (FStar_Pervasives_Native.Some head1)
                         env fvs (FStar_Syntax_Util.comp_result cres) in
                     (match uu____14400 with
                      | (rt, g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt in
                          let uu____14414 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____14430 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____14430 in
                                (cres1, g)
                            | uu____14431 ->
                                let g =
                                  let uu____14441 =
                                    let uu____14442 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard in
                                    FStar_All.pipe_right uu____14442
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env) in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____14441 in
                                let uu____14443 =
                                  let uu____14444 =
                                    FStar_Syntax_Util.arrow bs cres1 in
                                  FStar_Syntax_Syntax.mk_Total uu____14444 in
                                (uu____14443, g) in
                          (match uu____14414 with
                           | (cres2, guard1) ->
                               ((let uu____14454 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium in
                                 if uu____14454
                                 then
                                   let uu____14455 =
                                     FStar_Syntax_Print.comp_to_string cres2 in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____14455
                                 else ());
                                (let uu____14457 =
                                   let uu____14462 =
                                     let uu____14463 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         chead1 in
                                     FStar_All.pipe_right uu____14463
                                       FStar_TypeChecker_Common.lcomp_of_comp in
                                   let uu____14464 =
                                     let uu____14465 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         cres2 in
                                     FStar_All.pipe_right uu____14465
                                       FStar_TypeChecker_Common.lcomp_of_comp in
                                   (uu____14462, uu____14464) in
                                 match uu____14457 with
                                 | (chead2, cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____14488 ->
                                                 match uu____14488 with
                                                 | (uu____14497, uu____14498,
                                                    lc) ->
                                                     (let uu____14506 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc in
                                                      Prims.op_Negation
                                                        uu____14506)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev) in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head1
                                           (FStar_List.rev arg_rets_rev)
                                           head1.FStar_Syntax_Syntax.pos in
                                       let uu____14516 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful in
                                       if uu____14516
                                       then
                                         ((let uu____14518 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____14518
                                           then
                                             let uu____14519 =
                                               FStar_Syntax_Print.term_to_string
                                                 term in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____14519
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____14523 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____14523
                                           then
                                             let uu____14524 =
                                               FStar_Syntax_Print.term_to_string
                                                 term in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____14524
                                           else ());
                                          cres3) in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c ->
                                            fun uu____14552 ->
                                              match uu____14552 with
                                              | ((e, q), x, c) ->
                                                  ((let uu____14594 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14594
                                                    then
                                                      let uu____14595 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                            -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1 in
                                                      let uu____14597 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e in
                                                      let uu____14598 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____14595
                                                        uu____14597
                                                        uu____14598
                                                    else ());
                                                   (let uu____14600 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c in
                                                    if uu____14600
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
                                         arg_comps_rev in
                                     let comp1 =
                                       (let uu____14608 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme in
                                        if uu____14608
                                        then
                                          let uu____14609 =
                                            FStar_Syntax_Print.term_to_string
                                              head1 in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____14609
                                        else ());
                                       (let uu____14611 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2 in
                                        if uu____14611
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
                                              comp)) in
                                     let shortcuts_evaluation_order =
                                       let uu____14618 =
                                         let uu____14619 =
                                           FStar_Syntax_Subst.compress head1 in
                                         uu____14619.FStar_Syntax_Syntax.n in
                                       match uu____14618 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____14623 -> false in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1 ->
                                                fun uu____14644 ->
                                                  match uu____14644 with
                                                  | (arg, uu____14658,
                                                     uu____14659) -> arg ::
                                                      args1) [] arg_comps_rev in
                                         let app =
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             head1 args1 r in
                                         let app1 =
                                           FStar_TypeChecker_Util.maybe_lift
                                             env app
                                             cres4.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.res_typ in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env app1
                                           comp1.FStar_TypeChecker_Common.eff_name
                                           comp1.FStar_TypeChecker_Common.res_typ
                                       else
                                         (let uu____14667 =
                                            let map_fun uu____14733 =
                                              match uu____14733 with
                                              | ((e, q), uu____14774, c) ->
                                                  ((let uu____14797 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14797
                                                    then
                                                      let uu____14798 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e in
                                                      let uu____14799 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____14798
                                                        uu____14799
                                                    else ());
                                                   (let uu____14801 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c in
                                                    if uu____14801
                                                    then
                                                      ((let uu____14825 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme in
                                                        if uu____14825
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
                                                           (let uu____14860 =
                                                              let uu____14861
                                                                =
                                                                let uu____14862
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head1 in
                                                                uu____14862.FStar_Syntax_Syntax.n in
                                                              match uu____14861
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____14866
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore" in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____14866
                                                              | uu____14867
                                                                  -> true in
                                                            Prims.op_Negation
                                                              uu____14860) in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____14869 =
                                                            let uu____14874 =
                                                              let uu____14875
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e in
                                                              let uu____14876
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  c.FStar_TypeChecker_Common.eff_name in
                                                              let uu____14877
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____14875
                                                                uu____14876
                                                                uu____14877 in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____14874) in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____14869)
                                                       else ();
                                                       (let uu____14880 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme in
                                                        if uu____14880
                                                        then
                                                          FStar_Util.print_string
                                                            "... lifting!\n"
                                                        else ());
                                                       (let x =
                                                          FStar_Syntax_Syntax.new_bv
                                                            FStar_Pervasives_Native.None
                                                            c.FStar_TypeChecker_Common.res_typ in
                                                        let e1 =
                                                          FStar_TypeChecker_Util.maybe_lift
                                                            env e
                                                            c.FStar_TypeChecker_Common.eff_name
                                                            comp1.FStar_TypeChecker_Common.eff_name
                                                            c.FStar_TypeChecker_Common.res_typ in
                                                        let uu____14884 =
                                                          let uu____14893 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          (uu____14893, q) in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____14884))))) in
                                            let uu____14922 =
                                              let uu____14953 =
                                                let uu____14982 =
                                                  let uu____14993 =
                                                    let uu____15002 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head1 in
                                                    (uu____15002,
                                                      FStar_Pervasives_Native.None,
                                                      chead2) in
                                                  uu____14993 ::
                                                    arg_comps_rev in
                                                FStar_List.map map_fun
                                                  uu____14982 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____14953 in
                                            match uu____14922 with
                                            | (lifted_args, reverse_args) ->
                                                let uu____15203 =
                                                  let uu____15204 =
                                                    FStar_List.hd
                                                      reverse_args in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15204 in
                                                let uu____15225 =
                                                  let uu____15226 =
                                                    FStar_List.tl
                                                      reverse_args in
                                                  FStar_List.rev uu____15226 in
                                                (lifted_args, uu____15203,
                                                  uu____15225) in
                                          match uu____14667 with
                                          | (lifted_args, head2, args1) ->
                                              let app =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  head2 args1 r in
                                              let app1 =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env app
                                                  cres4.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ in
                                              let app2 =
                                                FStar_TypeChecker_Util.maybe_monadic
                                                  env app1
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ in
                                              let bind_lifted_args e
                                                uu___6_15335 =
                                                match uu___6_15335 with
                                                | FStar_Pervasives_Native.None
                                                    -> e
                                                | FStar_Pervasives_Native.Some
                                                    (x, m, t, e1) ->
                                                    let lb =
                                                      FStar_Syntax_Util.mk_letbinding
                                                        (FStar_Util.Inl x) []
                                                        t m e1 []
                                                        e1.FStar_Syntax_Syntax.pos in
                                                    let letbinding =
                                                      let uu____15396 =
                                                        let uu____15397 =
                                                          let uu____15410 =
                                                            let uu____15413 =
                                                              let uu____15414
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x in
                                                              [uu____15414] in
                                                            FStar_Syntax_Subst.close
                                                              uu____15413 e in
                                                          ((false, [lb]),
                                                            uu____15410) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____15397 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____15396
                                                        e.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (letbinding,
                                                           (FStar_Syntax_Syntax.Meta_monadic
                                                              (m,
                                                                (comp1.FStar_TypeChecker_Common.res_typ)))))
                                                      e.FStar_Syntax_Syntax.pos in
                                              FStar_List.fold_left
                                                bind_lifted_args app2
                                                lifted_args) in
                                     let uu____15463 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1 in
                                     (match uu____15463 with
                                      | (comp2, g) ->
                                          ((let uu____15480 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme in
                                            if uu____15480
                                            then
                                              let uu____15481 =
                                                FStar_Syntax_Print.term_to_string
                                                  app in
                                              let uu____15482 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____15481 uu____15482
                                            else ());
                                           (app, comp2, g))))))) in
               let rec tc_args head_info uu____15568 bs args1 =
                 match uu____15568 with
                 | (subst, outargs, arg_rets, g, fvs) ->
                     (match (bs, args1) with
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15731))::rest,
                         (uu____15733, FStar_Pervasives_Native.None)::uu____15734)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort in
                          let uu____15794 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head) env fvs t in
                          (match uu____15794 with
                           | (t1, g_ex) ->
                               let r1 =
                                 match outargs with
                                 | [] -> head.FStar_Syntax_Syntax.pos
                                 | ((t2, uu____15825), uu____15826,
                                    uu____15827)::uu____15828 ->
                                     let uu____15883 =
                                       FStar_Range.def_range
                                         head.FStar_Syntax_Syntax.pos in
                                     let uu____15884 =
                                       let uu____15885 =
                                         FStar_Range.use_range
                                           head.FStar_Syntax_Syntax.pos in
                                       let uu____15886 =
                                         FStar_Range.use_range
                                           t2.FStar_Syntax_Syntax.pos in
                                       FStar_Range.union_rng uu____15885
                                         uu____15886 in
                                     FStar_Range.range_of_rng uu____15883
                                       uu____15884 in
                               let uu____15887 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   r1 env t1 in
                               (match uu____15887 with
                                | (varg, uu____15907, implicits) ->
                                    let subst1 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst in
                                    let arg =
                                      let uu____15935 =
                                        FStar_Syntax_Syntax.as_implicit true in
                                      (varg, uu____15935) in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits in
                                    let uu____15943 =
                                      let uu____15986 =
                                        let uu____16005 =
                                          let uu____16022 =
                                            let uu____16023 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_All.pipe_right uu____16023
                                              FStar_TypeChecker_Common.lcomp_of_comp in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____16022) in
                                        uu____16005 :: outargs in
                                      (subst1, uu____15986, (arg ::
                                        arg_rets), guard, fvs) in
                                    tc_args head_info uu____15943 rest args1))
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau_or_attr))::rest,
                         (uu____16093, FStar_Pervasives_Native.None)::uu____16094)
                          ->
                          let uu____16153 =
                            match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let tau1 = FStar_Syntax_Subst.subst subst tau in
                                let uu____16166 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau1 in
                                (match uu____16166 with
                                 | (tau2, uu____16178, g_tau) ->
                                     let uu____16180 =
                                       let uu____16181 =
                                         let uu____16188 =
                                           FStar_Dyn.mkdyn env in
                                         (uu____16188, tau2) in
                                       FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                         uu____16181 in
                                     (uu____16180, g_tau))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let attr1 =
                                  FStar_Syntax_Subst.subst subst attr in
                                let uu____16195 =
                                  tc_tot_or_gtot_term env attr1 in
                                (match uu____16195 with
                                 | (attr2, uu____16207, g_attr) ->
                                     ((FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                         attr2), g_attr)) in
                          (match uu____16153 with
                           | (ctx_uvar_meta, g_tau_or_attr) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____16218 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head) env
                                   fvs t in
                               (match uu____16218 with
                                | (t1, g_ex) ->
                                    let r1 =
                                      match outargs with
                                      | [] -> head.FStar_Syntax_Syntax.pos
                                      | ((t2, uu____16249), uu____16250,
                                         uu____16251)::uu____16252 ->
                                          let uu____16307 =
                                            FStar_Range.def_range
                                              head.FStar_Syntax_Syntax.pos in
                                          let uu____16308 =
                                            let uu____16309 =
                                              FStar_Range.use_range
                                                head.FStar_Syntax_Syntax.pos in
                                            let uu____16310 =
                                              FStar_Range.use_range
                                                t2.FStar_Syntax_Syntax.pos in
                                            FStar_Range.union_rng uu____16309
                                              uu____16310 in
                                          FStar_Range.range_of_rng
                                            uu____16307 uu____16308 in
                                    let uu____16311 =
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        r1 env t1 FStar_Syntax_Syntax.Strict
                                        (FStar_Pervasives_Native.Some
                                           ctx_uvar_meta) in
                                    (match uu____16311 with
                                     | (varg, uu____16331, implicits) ->
                                         let subst1 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst in
                                         let arg =
                                           let uu____16359 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true in
                                           (varg, uu____16359) in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau_or_attr]
                                             implicits in
                                         let uu____16367 =
                                           let uu____16410 =
                                             let uu____16429 =
                                               let uu____16446 =
                                                 let uu____16447 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1 in
                                                 FStar_All.pipe_right
                                                   uu____16447
                                                   FStar_TypeChecker_Common.lcomp_of_comp in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16446) in
                                             uu____16429 :: outargs in
                                           (subst1, uu____16410, (arg ::
                                             arg_rets), guard, fvs) in
                                         tc_args head_info uu____16367 rest
                                           args1)))
                      | ((x, aqual)::rest, (e, aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16587, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16588)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16595),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16596)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16601),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16602)) ->
                                ()
                            | (FStar_Pervasives_Native.None,
                               FStar_Pervasives_Native.None) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality),
                               FStar_Pervasives_Native.None) -> ()
                            | uu____16615 ->
                                let uu____16624 =
                                  let uu____16629 =
                                    let uu____16630 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual in
                                    let uu____16631 =
                                      FStar_Syntax_Print.aqual_to_string aq in
                                    let uu____16632 =
                                      FStar_Syntax_Print.bv_to_string x in
                                    let uu____16633 =
                                      FStar_Syntax_Print.term_to_string e in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____16630 uu____16631 uu____16632
                                      uu____16633 in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____16629) in
                                FStar_Errors.raise_error uu____16624
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst aqual in
                            let x1 =
                              let uu___2346_16637 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2346_16637.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2346_16637.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____16639 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____16639
                             then
                               let uu____16640 =
                                 FStar_Syntax_Print.bv_to_string x1 in
                               let uu____16641 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort in
                               let uu____16642 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____16643 =
                                 FStar_Syntax_Print.subst_to_string subst in
                               let uu____16644 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____16640 uu____16641 uu____16642
                                 uu____16643 uu____16644
                             else ());
                            (let uu____16646 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head) env fvs
                                 targ in
                             match uu____16646 with
                             | (targ1, g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1 in
                                 let env2 =
                                   let uu___2355_16661 = env1 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2355_16661.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2355_16661.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2355_16661.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2355_16661.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2355_16661.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2355_16661.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2355_16661.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2355_16661.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2355_16661.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2355_16661.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2355_16661.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2355_16661.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2355_16661.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2355_16661.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2355_16661.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2355_16661.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___2355_16661.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2355_16661.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2355_16661.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2355_16661.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2355_16661.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2355_16661.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2355_16661.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2355_16661.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2355_16661.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2355_16661.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2355_16661.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2355_16661.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2355_16661.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2355_16661.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2355_16661.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2355_16661.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2355_16661.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2355_16661.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2355_16661.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2355_16661.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2355_16661.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2355_16661.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2355_16661.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2355_16661.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2355_16661.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2355_16661.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2355_16661.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2355_16661.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2355_16661.FStar_TypeChecker_Env.erasable_types_tab);
                                     FStar_TypeChecker_Env.enable_defer_to_tac
                                       =
                                       (uu___2355_16661.FStar_TypeChecker_Env.enable_defer_to_tac)
                                   } in
                                 ((let uu____16663 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High in
                                   if uu____16663
                                   then
                                     let uu____16664 =
                                       FStar_Syntax_Print.tag_of_term e in
                                     let uu____16665 =
                                       FStar_Syntax_Print.term_to_string e in
                                     let uu____16666 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1 in
                                     let uu____16667 =
                                       FStar_Util.string_of_bool
                                         env2.FStar_TypeChecker_Env.use_eq in
                                     FStar_Util.print4
                                       "Checking arg (%s) %s at type %s with use_eq:%s\n"
                                       uu____16664 uu____16665 uu____16666
                                       uu____16667
                                   else ());
                                  (let uu____16669 = tc_term env2 e in
                                   match uu____16669 with
                                   | (e1, c, g_e) ->
                                       let g1 =
                                         let uu____16686 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____16686 in
                                       let arg = (e1, aq) in
                                       let xterm =
                                         let uu____16709 =
                                           let uu____16712 =
                                             let uu____16721 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16721 in
                                           FStar_Pervasives_Native.fst
                                             uu____16712 in
                                         (uu____16709, aq) in
                                       let uu____16730 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name) in
                                       if uu____16730
                                       then
                                         let subst1 =
                                           let uu____16738 = FStar_List.hd bs in
                                           maybe_extend_subst subst
                                             uu____16738 e1 in
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
                      | (uu____16884, []) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([], arg::uu____16920) ->
                          let uu____16971 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs [] in
                          (match uu____16971 with
                           | (head1, chead1, ghead1) ->
                               let uu____16993 =
                                 let uu____16998 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1 in
                                 FStar_All.pipe_right uu____16998
                                   (fun uu____17015 ->
                                      match uu____17015 with
                                      | (c, g1) ->
                                          let uu____17026 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1 in
                                          (c, uu____17026)) in
                               (match uu____16993 with
                                | (chead2, ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____17065 =
                                          FStar_Syntax_Subst.compress tres in
                                        FStar_All.pipe_right uu____17065
                                          FStar_Syntax_Util.unrefine in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1, cres') ->
                                          let uu____17096 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres' in
                                          (match uu____17096 with
                                           | (bs2, cres'1) ->
                                               let head_info1 =
                                                 (head1, chead2, ghead3,
                                                   cres'1) in
                                               ((let uu____17119 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low in
                                                 if uu____17119
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
                                      | uu____17177 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____17185 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env) in
                                              FStar_All.pipe_right
                                                uu____17185
                                                FStar_Syntax_Util.unascribe in
                                            let uu____17186 =
                                              let uu____17187 =
                                                FStar_Syntax_Subst.compress
                                                  tres3 in
                                              uu____17187.FStar_Syntax_Syntax.n in
                                            match uu____17186 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____17190;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____17191;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},
                                                 uu____17193)
                                                -> norm_tres tres4
                                            | uu____17200 -> tres3 in
                                          let uu____17201 = norm_tres tres1 in
                                          aux true solve ghead3 uu____17201
                                      | uu____17202 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3 in
                                          aux norm1 true ghead4 tres1
                                      | uu____17204 ->
                                          let uu____17205 =
                                            let uu____17210 =
                                              let uu____17211 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead in
                                              let uu____17212 =
                                                FStar_Util.string_of_int
                                                  n_args in
                                              let uu____17213 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____17211 uu____17212
                                                uu____17213 in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____17210) in
                                          let uu____17214 =
                                            FStar_Syntax_Syntax.argpos arg in
                                          FStar_Errors.raise_error
                                            uu____17205 uu____17214 in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2)))) in
               let rec check_function_app tf guard =
                 let uu____17242 =
                   let uu____17243 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____17243.FStar_Syntax_Syntax.n in
                 match uu____17242 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____17252 ->
                     let uu____17265 =
                       FStar_List.fold_right
                         (fun uu____17296 ->
                            fun uu____17297 ->
                              match uu____17297 with
                              | (bs, guard1) ->
                                  let uu____17324 =
                                    let uu____17337 =
                                      let uu____17338 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____17338
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17337 in
                                  (match uu____17324 with
                                   | (t, uu____17354, g) ->
                                       let uu____17368 =
                                         let uu____17371 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____17371 :: bs in
                                       let uu____17372 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____17368, uu____17372))) args
                         ([], guard) in
                     (match uu____17265 with
                      | (bs, guard1) ->
                          let uu____17389 =
                            let uu____17396 =
                              let uu____17409 =
                                let uu____17410 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____17410
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17409 in
                            match uu____17396 with
                            | (t, uu____17426, g) ->
                                let uu____17440 = FStar_Options.ml_ish () in
                                if uu____17440
                                then
                                  let uu____17447 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____17450 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____17447, uu____17450)
                                else
                                  (let uu____17454 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____17457 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____17454, uu____17457)) in
                          (match uu____17389 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____17476 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____17476
                                 then
                                   let uu____17477 =
                                     FStar_Syntax_Print.term_to_string head in
                                   let uu____17478 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____17479 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17477 uu____17478 uu____17479
                                 else ());
                                (let g =
                                   let uu____17482 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17482 in
                                 let uu____17483 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____17483))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17484;
                        FStar_Syntax_Syntax.pos = uu____17485;
                        FStar_Syntax_Syntax.vars = uu____17486;_},
                      uu____17487)
                     ->
                     let uu____17524 =
                       FStar_List.fold_right
                         (fun uu____17555 ->
                            fun uu____17556 ->
                              match uu____17556 with
                              | (bs, guard1) ->
                                  let uu____17583 =
                                    let uu____17596 =
                                      let uu____17597 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____17597
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17596 in
                                  (match uu____17583 with
                                   | (t, uu____17613, g) ->
                                       let uu____17627 =
                                         let uu____17630 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____17630 :: bs in
                                       let uu____17631 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____17627, uu____17631))) args
                         ([], guard) in
                     (match uu____17524 with
                      | (bs, guard1) ->
                          let uu____17648 =
                            let uu____17655 =
                              let uu____17668 =
                                let uu____17669 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____17669
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17668 in
                            match uu____17655 with
                            | (t, uu____17685, g) ->
                                let uu____17699 = FStar_Options.ml_ish () in
                                if uu____17699
                                then
                                  let uu____17706 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____17709 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____17706, uu____17709)
                                else
                                  (let uu____17713 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____17716 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____17713, uu____17716)) in
                          (match uu____17648 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____17735 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____17735
                                 then
                                   let uu____17736 =
                                     FStar_Syntax_Print.term_to_string head in
                                   let uu____17737 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____17738 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17736 uu____17737 uu____17738
                                 else ());
                                (let g =
                                   let uu____17741 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17741 in
                                 let uu____17742 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____17742))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                     let uu____17765 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____17765 with
                      | (bs1, c1) ->
                          let head_info = (head, chead, ghead, c1) in
                          ((let uu____17788 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme in
                            if uu____17788
                            then
                              let uu____17789 =
                                FStar_Syntax_Print.term_to_string head in
                              let uu____17790 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____17791 =
                                FStar_Syntax_Print.binders_to_string ", " bs1 in
                              let uu____17792 =
                                FStar_Syntax_Print.comp_to_string c1 in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17789 uu____17790 uu____17791
                                uu____17792
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv, uu____17851) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t, uu____17857, uu____17858) ->
                     check_function_app t guard
                 | uu____17899 ->
                     let uu____17900 =
                       FStar_TypeChecker_Err.expected_function_typ env tf in
                     FStar_Errors.raise_error uu____17900
                       head.FStar_Syntax_Syntax.pos in
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
  fun env ->
    fun head ->
      fun chead ->
        fun g_head ->
          fun args ->
            fun expected_topt ->
              let r = FStar_TypeChecker_Env.get_range env in
              let tf =
                FStar_Syntax_Subst.compress
                  (FStar_Syntax_Util.comp_result chead) in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c in
                  let uu____17982 =
                    FStar_List.fold_left2
                      (fun uu____18049 ->
                         fun uu____18050 ->
                           fun uu____18051 ->
                             match (uu____18049, uu____18050, uu____18051)
                             with
                             | ((seen, guard, ghost), (e, aq), (b, aq')) ->
                                 ((let uu____18198 =
                                     let uu____18199 =
                                       FStar_Syntax_Util.eq_aqual aq aq' in
                                     uu____18199 <> FStar_Syntax_Util.Equal in
                                   if uu____18198
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____18201 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                       "arguments to short circuiting operators must be pure or ghost" in
                                   match uu____18201 with
                                   | (e1, c1, g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen in
                                       let g1 =
                                         let uu____18229 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____18229 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____18233 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____18233)
                                              &&
                                              (let uu____18235 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name in
                                               Prims.op_Negation uu____18235)) in
                                       let uu____18236 =
                                         let uu____18247 =
                                           let uu____18258 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____18258] in
                                         FStar_List.append seen uu____18247 in
                                       let uu____18291 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1 in
                                       (uu____18236, uu____18291, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____17982 with
                   | (args1, guard, ghost) ->
                       let e = FStar_Syntax_Syntax.mk_Tm_app head args1 r in
                       let c1 =
                         if ghost
                         then
                           let uu____18351 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____18351
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c in
                       let uu____18353 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____18353 with | (c2, g) -> (e, c2, g)))
              | uu____18369 ->
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
  fun env ->
    fun pat_t ->
      fun p0 ->
        let fail msg =
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MismatchedPatternType, msg)
            p0.FStar_Syntax_Syntax.p in
        let expected_pat_typ env1 pos scrutinee_t =
          let rec aux norm1 t =
            let t1 = FStar_Syntax_Util.unrefine t in
            let uu____18461 = FStar_Syntax_Util.head_and_args t1 in
            match uu____18461 with
            | (head, args) ->
                let uu____18504 =
                  let uu____18505 = FStar_Syntax_Subst.compress head in
                  uu____18505.FStar_Syntax_Syntax.n in
                (match uu____18504 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18509;
                        FStar_Syntax_Syntax.vars = uu____18510;_},
                      us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18517 ->
                     if norm1
                     then t1
                     else
                       (let uu____18519 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1 in
                        aux true uu____18519))
          and unfold_once t f us args =
            let uu____18536 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            if uu____18536
            then t
            else
              (let uu____18538 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               match uu____18538 with
               | FStar_Pervasives_Native.None -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____18558 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
                   (match uu____18558 with
                    | (uu____18563, head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            t.FStar_Syntax_Syntax.pos in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t' in
                        aux false t'1)) in
          let uu____18567 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t in
          aux false uu____18567 in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____18585 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____18585
           then
             let uu____18586 = FStar_Syntax_Print.term_to_string pat_t1 in
             let uu____18587 = FStar_Syntax_Print.term_to_string scrutinee_t in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____18586 uu____18587
           else ());
          (let fail1 msg =
             let msg1 =
               let uu____18601 = FStar_Syntax_Print.term_to_string pat_t1 in
               let uu____18602 =
                 FStar_Syntax_Print.term_to_string scrutinee_t in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____18601 uu____18602 msg in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p in
           let uu____18603 = FStar_Syntax_Util.head_and_args scrutinee_t in
           match uu____18603 with
           | (head_s, args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1 in
               let uu____18647 = FStar_Syntax_Util.un_uinst head_s in
               (match uu____18647 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____18648;
                    FStar_Syntax_Syntax.pos = uu____18649;
                    FStar_Syntax_Syntax.vars = uu____18650;_} ->
                    let uu____18653 = FStar_Syntax_Util.head_and_args pat_t2 in
                    (match uu____18653 with
                     | (head_p, args_p) ->
                         let uu____18696 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s in
                         if uu____18696
                         then
                           let uu____18697 =
                             let uu____18698 =
                               FStar_Syntax_Util.un_uinst head_p in
                             uu____18698.FStar_Syntax_Syntax.n in
                           (match uu____18697 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____18703 =
                                    let uu____18704 =
                                      let uu____18705 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____18705 in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____18704 in
                                  if uu____18703
                                  then
                                    fail1
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail1 ""
                                 else ();
                                 (let uu____18725 =
                                    let uu____18750 =
                                      let uu____18753 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18753 in
                                    match uu____18750 with
                                    | FStar_Pervasives_Native.None ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n ->
                                        let uu____18799 =
                                          FStar_Util.first_N n args_p in
                                        (match uu____18799 with
                                         | (params_p, uu____18857) ->
                                             let uu____18898 =
                                               FStar_Util.first_N n args_s in
                                             (match uu____18898 with
                                              | (params_s, uu____18956) ->
                                                  (params_p, params_s))) in
                                  match uu____18725 with
                                  | (params_p, params_s) ->
                                      FStar_List.fold_left2
                                        (fun out ->
                                           fun uu____19085 ->
                                             fun uu____19086 ->
                                               match (uu____19085,
                                                       uu____19086)
                                               with
                                               | ((p, uu____19120),
                                                  (s, uu____19122)) ->
                                                   let uu____19155 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s in
                                                   (match uu____19155 with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        let uu____19158 =
                                                          let uu____19159 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p in
                                                          let uu____19160 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____19159
                                                            uu____19160 in
                                                        fail1 uu____19158
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____19163 ->
                                fail1 "Pattern matching a non-inductive type")
                         else
                           (let uu____19165 =
                              let uu____19166 =
                                FStar_Syntax_Print.term_to_string head_p in
                              let uu____19167 =
                                FStar_Syntax_Print.term_to_string head_s in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____19166 uu____19167 in
                            fail1 uu____19165))
                | uu____19168 ->
                    let uu____19169 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t in
                    (match uu____19169 with
                     | FStar_Pervasives_Native.None -> fail1 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g in
                         g1))) in
        let type_of_simple_pat env1 e =
          let uu____19209 = FStar_Syntax_Util.head_and_args e in
          match uu____19209 with
          | (head, args) ->
              (match head.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____19277 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____19277 with
                    | (us, t_f) ->
                        let uu____19296 = FStar_Syntax_Util.arrow_formals t_f in
                        (match uu____19296 with
                         | (formals, t) ->
                             let erasable =
                               FStar_TypeChecker_Env.non_informative env1 t in
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____19401 formals1 args1 =
                                 match uu____19401 with
                                 | (subst, args_out, bvs, guard) ->
                                     (match (formals1, args1) with
                                      | ([], []) ->
                                          let head1 =
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              head us in
                                          let pat_e =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head1 args_out
                                              e.FStar_Syntax_Syntax.pos in
                                          let uu____19544 =
                                            FStar_Syntax_Subst.subst subst t in
                                          (pat_e, uu____19544, bvs, guard,
                                            erasable)
                                      | ((f1, uu____19548)::formals2,
                                         (a, imp_a)::args2) ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst
                                              f1.FStar_Syntax_Syntax.sort in
                                          let uu____19606 =
                                            let uu____19627 =
                                              let uu____19628 =
                                                FStar_Syntax_Subst.compress a in
                                              uu____19628.FStar_Syntax_Syntax.n in
                                            match uu____19627 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2662_19653 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2662_19653.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2662_19653.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      = t_f1
                                                  } in
                                                let a1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x1 in
                                                let subst1 =
                                                  (FStar_Syntax_Syntax.NT
                                                     (f1, a1))
                                                  :: subst in
                                                ((a1, imp_a), subst1,
                                                  (FStar_List.append bvs [x1]),
                                                  FStar_TypeChecker_Env.trivial_guard)
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____19676 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1 in
                                                let uu____19690 =
                                                  tc_tot_or_gtot_term env2 a in
                                                (match uu____19690 with
                                                 | (a1, uu____19718, g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g in
                                                     let subst1 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst in
                                                     ((a1, imp_a), subst1,
                                                       bvs, g1))
                                            | uu____19742 ->
                                                fail "Not a simple pattern" in
                                          (match uu____19606 with
                                           | (a1, subst1, bvs1, g) ->
                                               let uu____19803 =
                                                 let uu____19826 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard in
                                                 (subst1,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19826) in
                                               aux uu____19803 formals2 args2)
                                      | uu____19865 ->
                                          fail "Not a fully applued pattern") in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19920 -> fail "Not a simple pattern") in
        let rec check_nested_pattern env1 p t =
          (let uu____19982 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____19982
           then
             let uu____19983 = FStar_Syntax_Print.pat_to_string p in
             let uu____19984 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19983
               uu____19984
           else ());
          (let id =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____20005 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t in
               FStar_All.pipe_right uu____20005 FStar_Syntax_Syntax.mk_binder in
             let tm =
               let uu____20013 =
                 let uu____20014 =
                   let uu____20023 =
                     let uu____20024 =
                       FStar_All.pipe_right x_b FStar_Pervasives_Native.fst in
                     FStar_All.pipe_right uu____20024
                       FStar_Syntax_Syntax.bv_to_name in
                   FStar_All.pipe_right uu____20023
                     FStar_Syntax_Syntax.as_arg in
                 [uu____20014] in
               FStar_Syntax_Syntax.mk_Tm_app disc uu____20013
                 FStar_Range.dummyRange in
             let tm1 =
               let uu____20058 =
                 let uu____20059 =
                   FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg in
                 [uu____20059] in
               FStar_Syntax_Syntax.mk_Tm_app inner_t uu____20058
                 FStar_Range.dummyRange in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____20120 ->
               let uu____20127 =
                 let uu____20128 = FStar_Syntax_Print.pat_to_string p in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____20128 in
               failwith uu____20127
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2701_20147 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2701_20147.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2701_20147.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____20148 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], [id], uu____20148,
                 (let uu___2704_20154 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2704_20154.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2708_20157 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2708_20157.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2708_20157.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____20158 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], [id], uu____20158,
                 (let uu___2711_20164 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2711_20164.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant c ->
               ((match c with
                 | FStar_Const.Const_unit -> ()
                 | FStar_Const.Const_bool uu____20167 -> ()
                 | FStar_Const.Const_int uu____20168 -> ()
                 | FStar_Const.Const_char uu____20179 -> ()
                 | FStar_Const.Const_float uu____20180 -> ()
                 | FStar_Const.Const_string uu____20181 -> ()
                 | uu____20186 ->
                     let uu____20187 =
                       let uu____20188 = FStar_Syntax_Print.const_to_string c in
                       FStar_Util.format1
                         "Pattern matching a constant that does not have decidable equality: %s"
                         uu____20188 in
                     fail uu____20187);
                (let uu____20189 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p in
                 match uu____20189 with
                 | (uu____20216, e_c, uu____20218, uu____20219) ->
                     let uu____20224 = tc_tot_or_gtot_term env1 e_c in
                     (match uu____20224 with
                      | (e_c1, lc, g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                           (let expected_t =
                              expected_pat_typ env1 p0.FStar_Syntax_Syntax.p
                                t in
                            (let uu____20253 =
                               let uu____20254 =
                                 FStar_TypeChecker_Rel.teq_nosmt_force env1
                                   lc.FStar_TypeChecker_Common.res_typ
                                   expected_t in
                               Prims.op_Negation uu____20254 in
                             if uu____20253
                             then
                               let uu____20255 =
                                 let uu____20256 =
                                   FStar_Syntax_Print.term_to_string
                                     lc.FStar_TypeChecker_Common.res_typ in
                                 let uu____20257 =
                                   FStar_Syntax_Print.term_to_string
                                     expected_t in
                                 FStar_Util.format2
                                   "Type of pattern (%s) does not match type of scrutinee (%s)"
                                   uu____20256 uu____20257 in
                               fail uu____20255
                             else ());
                            ([], [], e_c1, p,
                              FStar_TypeChecker_Env.trivial_guard, false))))))
           | FStar_Syntax_Syntax.Pat_cons (fv, sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20309 ->
                        match uu____20309 with
                        | (p1, b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____20334
                                 -> (p1, b)
                             | uu____20343 ->
                                 let uu____20344 =
                                   let uu____20347 =
                                     let uu____20348 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun in
                                     FStar_Syntax_Syntax.Pat_var uu____20348 in
                                   FStar_Syntax_Syntax.withinfo uu____20347
                                     p1.FStar_Syntax_Syntax.p in
                                 (uu____20344, b))) sub_pats in
                 let uu___2752_20351 = p in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2752_20351.FStar_Syntax_Syntax.p)
                 } in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____20391 ->
                         match uu____20391 with
                         | (x, uu____20399) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____20404
                                  -> false
                              | uu____20411 -> true))) in
               let uu____20412 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat in
               (match uu____20412 with
                | (simple_bvs, simple_pat_e, g0, simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____20452 =
                          let uu____20453 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p in
                          let uu____20454 =
                            FStar_Syntax_Print.pat_to_string simple_pat in
                          let uu____20455 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1) in
                          let uu____20460 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs) in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____20453 uu____20454 uu____20455 uu____20460 in
                        failwith uu____20452)
                     else ();
                     (let uu____20462 =
                        let uu____20473 =
                          type_of_simple_pat env1 simple_pat_e in
                        match uu____20473 with
                        | (simple_pat_e1, simple_pat_t, simple_bvs1, guard,
                           erasable) ->
                            let g' =
                              let uu____20506 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t in
                              pat_typ_ok env1 simple_pat_t uu____20506 in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g' in
                            ((let uu____20509 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns") in
                              if uu____20509
                              then
                                let uu____20510 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1 in
                                let uu____20511 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t in
                                let uu____20512 =
                                  let uu____20513 =
                                    FStar_List.map
                                      (fun x ->
                                         let uu____20519 =
                                           let uu____20520 =
                                             FStar_Syntax_Print.bv_to_string
                                               x in
                                           let uu____20521 =
                                             let uu____20522 =
                                               let uu____20523 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort in
                                               Prims.op_Hat uu____20523 ")" in
                                             Prims.op_Hat " : " uu____20522 in
                                           Prims.op_Hat uu____20520
                                             uu____20521 in
                                         Prims.op_Hat "(" uu____20519)
                                      simple_bvs1 in
                                  FStar_All.pipe_right uu____20513
                                    (FStar_String.concat " ") in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____20510 uu____20511 uu____20512
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable)) in
                      match uu____20462 with
                      | (simple_pat_e1, simple_bvs1, g1, erasable) ->
                          let uu____20553 =
                            let uu____20582 =
                              let uu____20611 =
                                FStar_TypeChecker_Env.conj_guard g0 g1 in
                              (env1, [], [], [], [], uu____20611, erasable,
                                Prims.int_zero) in
                            FStar_List.fold_left2
                              (fun uu____20684 ->
                                 fun uu____20685 ->
                                   fun x ->
                                     match (uu____20684, uu____20685) with
                                     | ((env2, bvs, tms, pats, subst, g,
                                         erasable1, i),
                                        (p1, b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst
                                             x.FStar_Syntax_Syntax.sort in
                                         let uu____20846 =
                                           check_nested_pattern env2 p1
                                             expected_t in
                                         (match uu____20846 with
                                          | (bvs_p, tms_p, e_p, p2, g',
                                             erasable_p) ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____20910 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____20910 i in
                                                let uu____20911 =
                                                  let uu____20920 =
                                                    let uu____20925 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None in
                                                    mk_disc_t uu____20925 in
                                                  FStar_List.map uu____20920 in
                                                FStar_All.pipe_right tms_p
                                                  uu____20911 in
                                              let uu____20930 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g' in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append tms tms_p1),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst),
                                                uu____20930,
                                                (erasable1 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____20582 sub_pats1 simple_bvs1 in
                          (match uu____20553 with
                           | (_env, bvs, tms, checked_sub_pats, subst, g,
                              erasable1, uu____20980) ->
                               let pat_e =
                                 FStar_Syntax_Subst.subst subst simple_pat_e1 in
                               let reconstruct_nested_pat pat =
                                 let rec aux simple_pats bvs1 sub_pats2 =
                                   match simple_pats with
                                   | [] -> []
                                   | (hd, b)::simple_pats1 ->
                                       (match hd.FStar_Syntax_Syntax.v with
                                        | FStar_Syntax_Syntax.Pat_dot_term
                                            (x, e) ->
                                            let e1 =
                                              FStar_Syntax_Subst.subst subst
                                                e in
                                            let hd1 =
                                              let uu___2836_21137 = hd in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2836_21137.FStar_Syntax_Syntax.p)
                                              } in
                                            let uu____21142 =
                                              aux simple_pats1 bvs1 sub_pats2 in
                                            (hd1, b) :: uu____21142
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,
                                                (hd1, uu____21181)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____21213 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3 in
                                                 (hd1, b) :: uu____21213
                                             | uu____21230 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____21253 ->
                                            failwith
                                              "Impossible: expected a simple pattern") in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1, simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats in
                                     let uu___2857_21291 = pat in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2857_21291.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____21302 -> failwith "Impossible" in
                               let uu____21305 =
                                 reconstruct_nested_pat simple_pat_elab in
                               (bvs, tms, pat_e, uu____21305, g, erasable1)))))) in
        (let uu____21311 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns") in
         if uu____21311
         then
           let uu____21312 = FStar_Syntax_Print.pat_to_string p0 in
           FStar_Util.print1 "Checking pattern: %s\n" uu____21312
         else ());
        (let uu____21314 =
           let uu____21331 =
             let uu___2862_21332 =
               let uu____21333 = FStar_TypeChecker_Env.clear_expected_typ env in
               FStar_All.pipe_right uu____21333 FStar_Pervasives_Native.fst in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2862_21332.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2862_21332.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2862_21332.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2862_21332.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2862_21332.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2862_21332.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2862_21332.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2862_21332.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2862_21332.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2862_21332.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2862_21332.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2862_21332.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2862_21332.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2862_21332.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2862_21332.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2862_21332.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___2862_21332.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2862_21332.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2862_21332.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2862_21332.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2862_21332.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2862_21332.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2862_21332.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2862_21332.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2862_21332.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2862_21332.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2862_21332.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2862_21332.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2862_21332.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2862_21332.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2862_21332.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2862_21332.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2862_21332.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2862_21332.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2862_21332.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2862_21332.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2862_21332.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2862_21332.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2862_21332.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2862_21332.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2862_21332.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2862_21332.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2862_21332.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2862_21332.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2862_21332.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___2862_21332.FStar_TypeChecker_Env.enable_defer_to_tac)
             } in
           let uu____21348 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0 in
           check_nested_pattern uu____21331 uu____21348 pat_t in
         match uu____21314 with
         | (bvs, tms, pat_e, pat, g, erasable) ->
             ((let uu____21384 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns") in
               if uu____21384
               then
                 let uu____21385 = FStar_Syntax_Print.pat_to_string pat in
                 let uu____21386 = FStar_Syntax_Print.term_to_string pat_e in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____21385
                   uu____21386
               else ());
              (let uu____21388 = FStar_TypeChecker_Env.push_bvs env bvs in
               let uu____21389 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e in
               (pat, bvs, tms, uu____21388, pat_e, uu____21389, g, erasable))))
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
  fun scrutinee ->
    fun env ->
      fun branch ->
        let uu____21424 = FStar_Syntax_Subst.open_branch branch in
        match uu____21424 with
        | (pattern, when_clause, branch_exp) ->
            let uu____21471 = branch in
            (match uu____21471 with
             | (cpat, uu____21500, cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____21522 =
                   let uu____21529 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____21529
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____21522 with
                  | (scrutinee_env, uu____21564) ->
                      let uu____21569 = tc_pat env pat_t pattern in
                      (match uu____21569 with
                       | (pattern1, pat_bvs, pat_bv_tms, pat_env, pat_exp,
                          norm_pat_exp, guard_pat, erasable) ->
                           ((let uu____21634 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme in
                             if uu____21634
                             then
                               let uu____21635 =
                                 FStar_Syntax_Print.pat_to_string pattern1 in
                               let uu____21636 =
                                 FStar_Syntax_Print.bvs_to_string ";" pat_bvs in
                               let uu____21637 =
                                 FStar_List.fold_left
                                   (fun s ->
                                      fun t ->
                                        let uu____21643 =
                                          let uu____21644 =
                                            FStar_Syntax_Print.term_to_string
                                              t in
                                          Prims.op_Hat ";" uu____21644 in
                                        Prims.op_Hat s uu____21643) ""
                                   pat_bv_tms in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____21635 uu____21636 uu____21637
                             else ());
                            (let uu____21646 =
                               match when_clause with
                               | FStar_Pervasives_Native.None ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____21676 =
                                     FStar_TypeChecker_Env.should_verify env in
                                   if uu____21676
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____21694 =
                                        let uu____21701 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool in
                                        tc_term uu____21701 e in
                                      match uu____21694 with
                                      | (e1, c, g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g)) in
                             match uu____21646 with
                             | (when_clause1, g_when) ->
                                 let uu____21756 = tc_term pat_env branch_exp in
                                 (match uu____21756 with
                                  | (branch_exp1, c, g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____21812 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool in
                                              FStar_All.pipe_left
                                                (fun uu____21823 ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____21823) uu____21812 in
                                        let branch_guard =
                                          let uu____21827 =
                                            let uu____21828 =
                                              FStar_TypeChecker_Env.should_verify
                                                env in
                                            Prims.op_Negation uu____21828 in
                                          if uu____21827
                                          then
                                            FStar_Syntax_Util.exp_true_bool
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____21881 =
                                                   let uu____21888 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____21888 in
                                                 match uu____21881 with
                                                 | (is_induc, datacons) ->
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
                                                           f.FStar_Syntax_Syntax.v in
                                                       let uu____21900 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator in
                                                       (match uu____21900
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                            -> []
                                                        | uu____21921 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None in
                                                            let uu____21933 =
                                                              let uu____21934
                                                                =
                                                                let uu____21935
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2 in
                                                                [uu____21935] in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____21934
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                            [uu____21933])
                                                     else [] in
                                               let fail uu____21966 =
                                                 let uu____21967 =
                                                   let uu____21968 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos in
                                                   let uu____21969 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1 in
                                                   let uu____21970 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1 in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____21968 uu____21969
                                                     uu____21970 in
                                                 failwith uu____21967 in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1, uu____21983) ->
                                                     head_constructor t1
                                                 | uu____21988 -> fail () in
                                               let force_scrutinee
                                                 uu____21994 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     let uu____21995 =
                                                       let uu____21996 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p in
                                                       let uu____21997 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2 in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____21996
                                                         uu____21997 in
                                                     failwith uu____21995
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t in
                                               let pat_exp2 =
                                                 let uu____22002 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1 in
                                                 FStar_All.pipe_right
                                                   uu____22002
                                                   FStar_Syntax_Util.unmeta in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____22007,
                                                  FStar_Syntax_Syntax.Tm_name
                                                  uu____22008) -> []
                                               | (uu____22009,
                                                  FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,
                                                  FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____22012 =
                                                     let uu____22013 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1 in
                                                     let uu____22014 =
                                                       force_scrutinee () in
                                                     FStar_Syntax_Util.mk_decidable_eq
                                                       uu____22013
                                                       uu____22014 pat_exp2 in
                                                   [uu____22012]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____22017,
                                                   FStar_Pervasives_Native.Some
                                                   uu____22018)),
                                                  uu____22019) ->
                                                   let uu____22034 =
                                                     let uu____22041 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env in
                                                     match uu____22041 with
                                                     | (env1, uu____22055) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2 in
                                                   (match uu____22034 with
                                                    | (uu____22062, t,
                                                       uu____22064) ->
                                                        let uu____22065 =
                                                          let uu____22066 =
                                                            force_scrutinee
                                                              () in
                                                          FStar_Syntax_Util.mk_decidable_eq
                                                            t uu____22066
                                                            pat_exp2 in
                                                        [uu____22065])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22069, []),
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                  uu____22070) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2 in
                                                   let uu____22092 =
                                                     let uu____22093 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v in
                                                     Prims.op_Negation
                                                       uu____22093 in
                                                   if uu____22092
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22099 =
                                                        force_scrutinee () in
                                                      let uu____22102 =
                                                        head_constructor
                                                          pat_exp2 in
                                                      discriminate
                                                        uu____22099
                                                        uu____22102)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22105, []),
                                                  FStar_Syntax_Syntax.Tm_fvar
                                                  uu____22106) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2 in
                                                   let uu____22122 =
                                                     let uu____22123 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v in
                                                     Prims.op_Negation
                                                       uu____22123 in
                                                   if uu____22122
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22129 =
                                                        force_scrutinee () in
                                                      let uu____22132 =
                                                        head_constructor
                                                          pat_exp2 in
                                                      discriminate
                                                        uu____22129
                                                        uu____22132)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22135, pat_args),
                                                  FStar_Syntax_Syntax.Tm_app
                                                  (head, args)) ->
                                                   let f =
                                                     head_constructor head in
                                                   let uu____22180 =
                                                     (let uu____22183 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v in
                                                      Prims.op_Negation
                                                        uu____22183)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args)) in
                                                   if uu____22180
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____22206 =
                                                          let uu____22211 =
                                                            FStar_List.zip
                                                              pat_args args in
                                                          FStar_All.pipe_right
                                                            uu____22211
                                                            (FStar_List.mapi
                                                               (fun i ->
                                                                  fun
                                                                    uu____22293
                                                                    ->
                                                                    match uu____22293
                                                                    with
                                                                    | 
                                                                    ((pi,
                                                                    uu____22313),
                                                                    (ei,
                                                                    uu____22315))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____22340
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    match uu____22340
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____22361
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____22373
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____22373
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____22374
                                                                    =
                                                                    let uu____22375
                                                                    =
                                                                    let uu____22376
                                                                    =
                                                                    let uu____22385
                                                                    =
                                                                    force_scrutinee
                                                                    () in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____22385 in
                                                                    [uu____22376] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____22375
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____22374 in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei)) in
                                                        FStar_All.pipe_right
                                                          uu____22206
                                                          FStar_List.flatten in
                                                      let uu____22408 =
                                                        let uu____22411 =
                                                          force_scrutinee () in
                                                        discriminate
                                                          uu____22411 f in
                                                      FStar_List.append
                                                        uu____22408
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____22414, uu____22415)
                                                   -> []
                                               | uu____22422 ->
                                                   let uu____22427 =
                                                     let uu____22428 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2 in
                                                     let uu____22429 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2 in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____22428
                                                       uu____22429 in
                                                   failwith uu____22427 in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____22456 =
                                                 let uu____22457 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____22457 in
                                               if uu____22456
                                               then
                                                 FStar_Syntax_Util.exp_true_bool
                                               else
                                                 (let t =
                                                    let uu____22460 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_and_l
                                                      uu____22460 in
                                                  let uu____22469 =
                                                    tc_check_tot_or_gtot_term
                                                      scrutinee_env t
                                                      FStar_Syntax_Util.t_bool
                                                      "" in
                                                  match uu____22469 with
                                                  | (t1, uu____22477,
                                                     uu____22478) -> t1) in
                                             let branch_guard =
                                               build_and_check_branch_guard
                                                 (FStar_Pervasives_Native.Some
                                                    scrutinee_tm) pattern1
                                                 norm_pat_exp in
                                             let branch_guard1 =
                                               match when_condition with
                                               | FStar_Pervasives_Native.None
                                                   -> branch_guard
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   FStar_Syntax_Util.mk_and
                                                     branch_guard w in
                                             branch_guard1) in
                                        (let uu____22493 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             FStar_Options.Extreme in
                                         if uu____22493
                                         then
                                           let uu____22494 =
                                             FStar_Syntax_Print.term_to_string
                                               branch_guard in
                                           FStar_Util.print1
                                             "tc_eqn: branch guard : %s\n"
                                             uu____22494
                                         else ());
                                        (let uu____22496 =
                                           let eqs =
                                             let uu____22515 =
                                               let uu____22516 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env in
                                               Prims.op_Negation uu____22516 in
                                             if uu____22515
                                             then
                                               FStar_Pervasives_Native.None
                                             else
                                               (let e =
                                                  FStar_Syntax_Subst.compress
                                                    pat_exp in
                                                let uu____22521 =
                                                  let uu____22522 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____22522 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____22521) in
                                           let uu____22523 =
                                             FStar_TypeChecker_Util.strengthen_precondition
                                               FStar_Pervasives_Native.None
                                               env branch_exp1 c g_branch in
                                           match uu____22523 with
                                           | (c1, g_branch1) ->
                                               let branch_has_layered_effect
                                                 =
                                                 let uu____22549 =
                                                   FStar_All.pipe_right
                                                     c1.FStar_TypeChecker_Common.eff_name
                                                     (FStar_TypeChecker_Env.norm_eff_name
                                                        env) in
                                                 FStar_All.pipe_right
                                                   uu____22549
                                                   (FStar_TypeChecker_Env.is_layered_effect
                                                      env) in
                                               let uu____22550 =
                                                 let env1 =
                                                   let uu____22556 =
                                                     FStar_All.pipe_right
                                                       pat_bvs
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder) in
                                                   FStar_TypeChecker_Env.push_binders
                                                     scrutinee_env
                                                     uu____22556 in
                                                 if branch_has_layered_effect
                                                 then
                                                   let c2 =
                                                     let uu____22564 =
                                                       let uu____22565 =
                                                         FStar_Syntax_Util.b2t
                                                           branch_guard in
                                                       FStar_TypeChecker_Common.NonTrivial
                                                         uu____22565 in
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env1 c1 uu____22564 in
                                                   (c2,
                                                     FStar_TypeChecker_Env.trivial_guard)
                                                 else
                                                   (match (eqs,
                                                            when_condition)
                                                    with
                                                    | uu____22577 when
                                                        let uu____22588 =
                                                          FStar_TypeChecker_Env.should_verify
                                                            env1 in
                                                        Prims.op_Negation
                                                          uu____22588
                                                        -> (c1, g_when)
                                                    | (FStar_Pervasives_Native.None,
                                                       FStar_Pervasives_Native.None)
                                                        -> (c1, g_when)
                                                    | (FStar_Pervasives_Native.Some
                                                       f,
                                                       FStar_Pervasives_Native.None)
                                                        ->
                                                        let gf =
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            f in
                                                        let g =
                                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                                            gf in
                                                        let uu____22608 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 gf in
                                                        let uu____22609 =
                                                          FStar_TypeChecker_Env.imp_guard
                                                            g g_when in
                                                        (uu____22608,
                                                          uu____22609)
                                                    | (FStar_Pervasives_Native.Some
                                                       f,
                                                       FStar_Pervasives_Native.Some
                                                       w) ->
                                                        let g_f =
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            f in
                                                        let g_fw =
                                                          let uu____22624 =
                                                            FStar_Syntax_Util.mk_conj
                                                              f w in
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            uu____22624 in
                                                        let uu____22625 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 g_fw in
                                                        let uu____22626 =
                                                          let uu____22627 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              g_f in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____22627
                                                            g_when in
                                                        (uu____22625,
                                                          uu____22626)
                                                    | (FStar_Pervasives_Native.None,
                                                       FStar_Pervasives_Native.Some
                                                       w) ->
                                                        let g_w =
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            w in
                                                        let g =
                                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                                            g_w in
                                                        let uu____22641 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 g_w in
                                                        (uu____22641, g_when)) in
                                               (match uu____22550 with
                                                | (c_weak, g_when_weak) ->
                                                    let binders =
                                                      FStar_List.map
                                                        FStar_Syntax_Syntax.mk_binder
                                                        pat_bvs in
                                                    let maybe_return_c_weak
                                                      should_return =
                                                      let c_weak1 =
                                                        let uu____22681 =
                                                          should_return &&
                                                            (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                               c_weak) in
                                                        if uu____22681
                                                        then
                                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                            env branch_exp1
                                                            c_weak
                                                        else c_weak in
                                                      if
                                                        branch_has_layered_effect
                                                      then
                                                        ((let uu____22684 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects") in
                                                          if uu____22684
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
                                                                    let uu____22696
                                                                    =
                                                                    let uu____22697
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    [uu____22697] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____22696
                                                                    FStar_Range.dummyRange)) in
                                                          let pat_bv_tms2 =
                                                            let env1 =
                                                              let uu___3093_22734
                                                                =
                                                                FStar_TypeChecker_Env.push_bv
                                                                  env
                                                                  scrutinee in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___3093_22734.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              } in
                                                            let uu____22735 =
                                                              let uu____22738
                                                                =
                                                                FStar_List.fold_left2
                                                                  (fun
                                                                    uu____22766
                                                                    ->
                                                                    fun
                                                                    pat_bv_tm
                                                                    ->
                                                                    fun bv ->
                                                                    match uu____22766
                                                                    with
                                                                    | 
                                                                    (substs,
                                                                    acc) ->
                                                                    let expected_t
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    substs
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    let pat_bv_tm1
                                                                    =
                                                                    let uu____22807
                                                                    =
                                                                    let uu____22814
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pat_bv_tm
                                                                    (FStar_Syntax_Subst.subst
                                                                    substs) in
                                                                    let uu____22815
                                                                    =
                                                                    let uu____22826
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t in
                                                                    tc_trivial_guard
                                                                    uu____22826 in
                                                                    FStar_All.pipe_right
                                                                    uu____22814
                                                                    uu____22815 in
                                                                    FStar_All.pipe_right
                                                                    uu____22807
                                                                    FStar_Pervasives_Native.fst in
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
                                                                  pat_bvs in
                                                              FStar_All.pipe_right
                                                                uu____22738
                                                                FStar_Pervasives_Native.snd in
                                                            FStar_All.pipe_right
                                                              uu____22735
                                                              (FStar_List.map
                                                                 (FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1)) in
                                                          (let uu____22888 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env)
                                                               (FStar_Options.Other
                                                                  "LayeredEffects") in
                                                           if uu____22888
                                                           then
                                                             let uu____22889
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun s ->
                                                                    fun t ->
                                                                    let uu____22895
                                                                    =
                                                                    let uu____22896
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____22896 in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____22895)
                                                                 ""
                                                                 pat_bv_tms2 in
                                                             let uu____22897
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun s ->
                                                                    fun t ->
                                                                    let uu____22903
                                                                    =
                                                                    let uu____22904
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____22904 in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____22903)
                                                                 "" pat_bvs in
                                                             FStar_Util.print2
                                                               "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                                                               uu____22889
                                                               uu____22897
                                                           else ());
                                                          (let uu____22906 =
                                                             FStar_All.pipe_right
                                                               c_weak1
                                                               (FStar_TypeChecker_Common.apply_lcomp
                                                                  (fun c2 ->
                                                                    c2)
                                                                  (fun g ->
                                                                    match eqs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    -> g
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    eqs1 ->
                                                                    FStar_TypeChecker_Common.weaken_guard_formula
                                                                    g eqs1)) in
                                                           let uu____22913 =
                                                             let uu____22918
                                                               =
                                                               FStar_TypeChecker_Env.push_bv
                                                                 env
                                                                 scrutinee in
                                                             FStar_TypeChecker_Util.close_layered_lcomp
                                                               uu____22918
                                                               pat_bvs
                                                               pat_bv_tms2 in
                                                           FStar_All.pipe_right
                                                             uu____22906
                                                             uu____22913)))
                                                      else
                                                        FStar_TypeChecker_Util.close_wp_lcomp
                                                          env pat_bvs c_weak1 in
                                                    let uu____22920 =
                                                      FStar_TypeChecker_Env.close_guard
                                                        env binders
                                                        g_when_weak in
                                                    let uu____22921 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        guard_pat g_branch1 in
                                                    ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                      (c_weak.FStar_TypeChecker_Common.cflags),
                                                      maybe_return_c_weak,
                                                      uu____22920,
                                                      uu____22921)) in
                                         match uu____22496 with
                                         | (effect_label, cflags,
                                            maybe_return_c, g_when1,
                                            g_branch1) ->
                                             let guard =
                                               FStar_TypeChecker_Env.conj_guard
                                                 g_when1 g_branch1 in
                                             ((let uu____22971 =
                                                 FStar_TypeChecker_Env.debug
                                                   env FStar_Options.High in
                                               if uu____22971
                                               then
                                                 let uu____22972 =
                                                   FStar_TypeChecker_Rel.guard_to_string
                                                     env guard in
                                                 FStar_All.pipe_left
                                                   (FStar_Util.print1
                                                      "Carrying guard from match: %s\n")
                                                   uu____22972
                                               else ());
                                              (let uu____22974 =
                                                 FStar_Syntax_Subst.close_branch
                                                   (pattern1, when_clause1,
                                                     branch_exp1) in
                                               let uu____22991 =
                                                 let uu____22992 =
                                                   FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder
                                                     pat_bvs in
                                                 FStar_TypeChecker_Util.close_guard_implicits
                                                   env false uu____22992
                                                   guard in
                                               (uu____22974, branch_guard,
                                                 effect_label, cflags,
                                                 maybe_return_c, uu____22991,
                                                 erasable))))))))))))
and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
          let uu____23035 = check_let_bound_def true env1 lb in
          (match uu____23035 with
           | (e1, univ_vars, c1, g1, annotated) ->
               let uu____23057 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____23078 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____23078, univ_vars, c1)
                 else
                   (let g11 =
                      let uu____23083 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____23083
                        (FStar_TypeChecker_Rel.resolve_implicits env1) in
                    let uu____23084 = FStar_TypeChecker_Common.lcomp_comp c1 in
                    match uu____23084 with
                    | (comp1, g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1 in
                        let uu____23102 =
                          let uu____23115 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)] in
                          FStar_List.hd uu____23115 in
                        (match uu____23102 with
                         | (uu____23164, univs, e11, c11, gvs) ->
                             let g13 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.map_guard g12)
                                 (FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta;
                                    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                    FStar_TypeChecker_Env.CompressUvars;
                                    FStar_TypeChecker_Env.NoFullNorm;
                                    FStar_TypeChecker_Env.Exclude
                                      FStar_TypeChecker_Env.Zeta] env1) in
                             let g14 =
                               FStar_TypeChecker_Env.abstract_guard_n gvs g13 in
                             let uu____23178 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11 in
                             (g14, e11, univs, uu____23178))) in
               (match uu____23057 with
                | (g11, e11, univ_vars1, c11) ->
                    let uu____23195 =
                      let uu____23204 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____23204
                      then
                        let uu____23213 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____23213 with
                        | (ok, c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____23242 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.log_issue uu____23242
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____23243 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____23243, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____23254 =
                            FStar_TypeChecker_Common.lcomp_comp c11 in
                          match uu____23254 with
                          | (comp1, g_comp1) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env1
                                 g_comp1;
                               (let c =
                                  FStar_All.pipe_right comp1
                                    (FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Env.Beta;
                                       FStar_TypeChecker_Env.NoFullNorm;
                                       FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                       env1) in
                                let e21 =
                                  let uu____23278 =
                                    FStar_Syntax_Util.is_pure_comp c in
                                  if uu____23278
                                  then e2
                                  else
                                    ((let uu____23283 =
                                        FStar_TypeChecker_Env.get_range env1 in
                                      FStar_Errors.log_issue uu____23283
                                        FStar_TypeChecker_Err.top_level_effect);
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Masked_effect)))
                                       e2.FStar_Syntax_Syntax.pos) in
                                (e21, c))))) in
                    (match uu____23195 with
                     | (e21, c12) ->
                         ((let uu____23307 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium in
                           if uu____23307
                           then
                             let uu____23308 =
                               FStar_Syntax_Print.term_to_string e11 in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____23308
                           else ());
                          (let e12 =
                             let uu____23311 = FStar_Options.tcnorm () in
                             if uu____23311
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
                             else e11 in
                           (let uu____23314 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium in
                            if uu____23314
                            then
                              let uu____23315 =
                                FStar_Syntax_Print.term_to_string e12 in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____23315
                            else ());
                           (let cres =
                              let uu____23318 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12 in
                              if uu____23318
                              then
                                FStar_Syntax_Syntax.mk_Total'
                                  FStar_Syntax_Syntax.t_unit
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.U_zero)
                              else
                                (let c1_comp_typ =
                                   FStar_All.pipe_right c12
                                     (FStar_TypeChecker_Env.unfold_effect_abbrev
                                        env1) in
                                 let c1_wp =
                                   match c1_comp_typ.FStar_Syntax_Syntax.effect_args
                                   with
                                   | (wp, uu____23323)::[] -> wp
                                   | uu____23348 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args" in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name in
                                 let wp2 =
                                   let ret =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_return_vc_combinator in
                                   let uu____23362 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [FStar_Syntax_Syntax.U_zero] env1
                                       c1_eff_decl ret in
                                   let uu____23363 =
                                     let uu____23364 =
                                       FStar_Syntax_Syntax.as_arg
                                         FStar_Syntax_Syntax.t_unit in
                                     let uu____23373 =
                                       let uu____23384 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.unit_const in
                                       [uu____23384] in
                                     uu____23364 :: uu____23373 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____23362
                                     uu____23363 e21.FStar_Syntax_Syntax.pos in
                                 let wp =
                                   let bind =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator in
                                   let uu____23419 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       (FStar_List.append
                                          c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                          [FStar_Syntax_Syntax.U_zero]) env1
                                       c1_eff_decl bind in
                                   let uu____23420 =
                                     let uu____23421 =
                                       let uu____23430 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_constant
                                              (FStar_Const.Const_range
                                                 (lb.FStar_Syntax_Syntax.lbpos)))
                                           lb.FStar_Syntax_Syntax.lbpos in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____23430 in
                                     let uu____23439 =
                                       let uu____23450 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           c1_comp_typ.FStar_Syntax_Syntax.result_typ in
                                       let uu____23467 =
                                         let uu____23478 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.t_unit in
                                         let uu____23487 =
                                           let uu____23498 =
                                             FStar_Syntax_Syntax.as_arg c1_wp in
                                           let uu____23507 =
                                             let uu____23518 =
                                               let uu____23527 =
                                                 let uu____23528 =
                                                   let uu____23529 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       c1_comp_typ.FStar_Syntax_Syntax.result_typ in
                                                   [uu____23529] in
                                                 FStar_Syntax_Util.abs
                                                   uu____23528 wp2
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Util.mk_residual_comp
                                                         FStar_Parser_Const.effect_Tot_lid
                                                         FStar_Pervasives_Native.None
                                                         [FStar_Syntax_Syntax.TOTAL])) in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23527 in
                                             [uu____23518] in
                                           uu____23498 :: uu____23507 in
                                         uu____23478 :: uu____23487 in
                                       uu____23450 :: uu____23467 in
                                     uu____23421 :: uu____23439 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____23419
                                     uu____23420 lb.FStar_Syntax_Syntax.lbpos in
                                 let uu____23606 =
                                   let uu____23607 =
                                     let uu____23618 =
                                       FStar_Syntax_Syntax.as_arg wp in
                                     [uu____23618] in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____23607;
                                     FStar_Syntax_Syntax.flags = []
                                   } in
                                 FStar_Syntax_Syntax.mk_Comp uu____23606) in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars1
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos in
                            let uu____23646 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                e.FStar_Syntax_Syntax.pos in
                            let uu____23657 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres in
                            (uu____23646, uu____23657,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____23658 -> failwith "Impossible"
and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lem_typ ->
      fun c2 ->
        let uu____23668 = FStar_Syntax_Util.is_smt_lemma lem_typ in
        if uu____23668
        then
          let universe_of_binders bs =
            let uu____23693 =
              FStar_List.fold_left
                (fun uu____23718 ->
                   fun b ->
                     match uu____23718 with
                     | (env1, us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b] in
                         (env2, (u :: us))) (env, []) bs in
            match uu____23693 with | (uu____23766, us) -> FStar_List.rev us in
          let quant =
            FStar_Syntax_Util.smt_lemma_as_forall lem_typ universe_of_binders in
          FStar_TypeChecker_Util.weaken_precondition env c2
            (FStar_TypeChecker_Common.NonTrivial quant)
        else c2
and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
          let env2 =
            let uu___3225_23798 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3225_23798.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3225_23798.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3225_23798.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3225_23798.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3225_23798.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3225_23798.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3225_23798.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3225_23798.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3225_23798.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3225_23798.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3225_23798.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3225_23798.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3225_23798.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3225_23798.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3225_23798.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3225_23798.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___3225_23798.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___3225_23798.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3225_23798.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3225_23798.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3225_23798.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3225_23798.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3225_23798.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3225_23798.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3225_23798.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3225_23798.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3225_23798.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3225_23798.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3225_23798.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3225_23798.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3225_23798.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3225_23798.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3225_23798.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3225_23798.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3225_23798.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3225_23798.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3225_23798.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3225_23798.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3225_23798.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3225_23798.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3225_23798.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3225_23798.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3225_23798.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3225_23798.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3225_23798.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___3225_23798.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let uu____23799 =
            let uu____23810 =
              let uu____23811 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____23811 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____23810 lb in
          (match uu____23799 with
           | (e1, uu____23833, c1, g1, annotated) ->
               let pure_or_ghost =
                 FStar_TypeChecker_Common.is_pure_or_ghost_lcomp c1 in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____23842 =
                     let uu____23847 =
                       let uu____23848 = FStar_Syntax_Print.term_to_string e1 in
                       let uu____23849 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____23848 uu____23849 in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____23847) in
                   FStar_Errors.raise_error uu____23842
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____23856 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ) in
                   if uu____23856
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs in
                 let x =
                   let uu___3240_23865 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3240_23865.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3240_23865.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   } in
                 let uu____23866 =
                   let uu____23871 =
                     let uu____23872 = FStar_Syntax_Syntax.mk_binder x in
                     [uu____23872] in
                   FStar_Syntax_Subst.open_term uu____23871 e2 in
                 match uu____23866 with
                 | (xb, e21) ->
                     let xbinder = FStar_List.hd xb in
                     let x1 = FStar_Pervasives_Native.fst xbinder in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1 in
                     let uu____23916 =
                       let uu____23923 = tc_term env_x e21 in
                       FStar_All.pipe_right uu____23923
                         (fun uu____23949 ->
                            match uu____23949 with
                            | (e22, c2, g2) ->
                                let uu____23965 =
                                  let uu____23970 =
                                    FStar_All.pipe_right
                                      (fun uu____23985 ->
                                         "folding guard g2 of e2 in the lcomp")
                                      (fun uu____23989 ->
                                         FStar_Pervasives_Native.Some
                                           uu____23989) in
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    uu____23970 env_x e22 c2 g2 in
                                (match uu____23965 with
                                 | (c21, g21) -> (e22, c21, g21))) in
                     (match uu____23916 with
                      | (e22, c2, g2) ->
                          let c21 =
                            maybe_intro_smt_lemma env_x
                              c1.FStar_TypeChecker_Common.res_typ c2 in
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c21) in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c21.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c21.FStar_TypeChecker_Common.res_typ in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_TypeChecker_Common.res_typ
                              cres.FStar_TypeChecker_Common.eff_name e11
                              attrs lb.FStar_Syntax_Syntax.lbpos in
                          let e3 =
                            let uu____24017 =
                              let uu____24018 =
                                let uu____24031 =
                                  FStar_Syntax_Subst.close xb e23 in
                                ((false, [lb1]), uu____24031) in
                              FStar_Syntax_Syntax.Tm_let uu____24018 in
                            FStar_Syntax_Syntax.mk uu____24017
                              e.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ in
                          let g21 =
                            let uu____24046 =
                              let uu____24047 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2) in
                              FStar_All.pipe_right uu____24047
                                (FStar_TypeChecker_Env.is_layered_effect env2) in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____24046 xb g2 in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g21 in
                          let uu____24049 =
                            let uu____24050 =
                              FStar_TypeChecker_Env.expected_typ env2 in
                            FStar_Option.isSome uu____24050 in
                          if uu____24049
                          then
                            let tt =
                              let uu____24060 =
                                FStar_TypeChecker_Env.expected_typ env2 in
                              FStar_All.pipe_right uu____24060
                                FStar_Option.get in
                            ((let uu____24066 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports") in
                              if uu____24066
                              then
                                let uu____24067 =
                                  FStar_Syntax_Print.term_to_string tt in
                                let uu____24068 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____24067 uu____24068
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____24071 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ in
                             match uu____24071 with
                             | (t, g_ex) ->
                                 ((let uu____24085 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports") in
                                   if uu____24085
                                   then
                                     let uu____24086 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ in
                                     let uu____24087 =
                                       FStar_Syntax_Print.term_to_string t in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____24086 uu____24087
                                   else ());
                                  (let uu____24089 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard in
                                   (e4,
                                     (let uu___3279_24091 = cres in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3279_24091.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3279_24091.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3279_24091.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____24089))))))))
      | uu____24092 ->
          failwith "Impossible (inner let with more than one lb)"
and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) ->
          let uu____24124 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____24124 with
           | (lbs1, e21) ->
               let uu____24143 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____24143 with
                | (env0, topt) ->
                    let uu____24162 = build_let_rec_env true env0 lbs1 in
                    (match uu____24162 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____24184 = check_let_recs rec_env lbs2 in
                         (match uu____24184 with
                          | (lbs3, g_lbs) ->
                              let g_lbs1 =
                                let uu____24204 =
                                  let uu____24205 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs in
                                  FStar_All.pipe_right uu____24205
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1) in
                                FStar_All.pipe_right uu____24204
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1) in
                              let all_lb_names =
                                let uu____24211 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____24211
                                  (fun uu____24228 ->
                                     FStar_Pervasives_Native.Some uu____24228) in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          let lbdef =
                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                              env1
                                              lb.FStar_Syntax_Syntax.lbdef in
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
                                     let uu____24261 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb ->
                                               let uu____24295 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____24295))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____24261 in
                                   FStar_List.map2
                                     (fun uu____24329 ->
                                        fun lb ->
                                          match uu____24329 with
                                          | (x, uvs, e, c, gvs) ->
                                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                all_lb_names x uvs
                                                (FStar_Syntax_Util.comp_result
                                                   c)
                                                (FStar_Syntax_Util.comp_effect_name
                                                   c) e
                                                lb.FStar_Syntax_Syntax.lbattrs
                                                lb.FStar_Syntax_Syntax.lbpos)
                                     ecs lbs3) in
                              let cres =
                                let uu____24377 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____24377 in
                              let uu____24378 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____24378 with
                               | (lbs5, e22) ->
                                   ((let uu____24398 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____24398
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____24399 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____24399, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____24410 -> failwith "Impossible"
and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) ->
          let uu____24442 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____24442 with
           | (lbs1, e21) ->
               let uu____24461 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____24461 with
                | (env0, topt) ->
                    let uu____24480 = build_let_rec_env false env0 lbs1 in
                    (match uu____24480 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____24502 =
                           let uu____24509 = check_let_recs rec_env lbs2 in
                           FStar_All.pipe_right uu____24509
                             (fun uu____24532 ->
                                match uu____24532 with
                                | (lbs3, g) ->
                                    let uu____24551 =
                                      FStar_TypeChecker_Env.conj_guard g_t g in
                                    (lbs3, uu____24551)) in
                         (match uu____24502 with
                          | (lbs3, g_lbs) ->
                              let uu____24566 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2 ->
                                        fun lb ->
                                          let x =
                                            let uu___3354_24589 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3354_24589.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3354_24589.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___3357_24591 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3357_24591.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3357_24591.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3357_24591.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3357_24591.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3357_24591.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3357_24591.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____24566 with
                               | (env2, lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____24618 = tc_term env2 e21 in
                                   (match uu____24618 with
                                    | (e22, cres, g2) ->
                                        let cres1 =
                                          FStar_List.fold_right
                                            (fun lb ->
                                               fun cres1 ->
                                                 maybe_intro_smt_lemma env2
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                   cres1) lbs4 cres in
                                        let cres2 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres1 in
                                        let cres3 =
                                          FStar_TypeChecker_Common.lcomp_set_flags
                                            cres2
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE] in
                                        let guard =
                                          let uu____24642 =
                                            let uu____24643 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____24643 g2 in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____24642 in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_wp_lcomp
                                            env2 bvs cres3 in
                                        let tres =
                                          norm env2
                                            cres4.FStar_TypeChecker_Common.res_typ in
                                        let cres5 =
                                          let uu___3378_24653 = cres4 in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3378_24653.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3378_24653.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3378_24653.FStar_TypeChecker_Common.comp_thunk)
                                          } in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb ->
                                                    let uu____24661 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____24661)) in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard in
                                        let uu____24662 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____24662 with
                                         | (lbs5, e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____24700 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  let uu____24701 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  (match uu____24701 with
                                                   | (tres1, g_ex) ->
                                                       let cres6 =
                                                         let uu___3394_24715
                                                           = cres5 in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3394_24715.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3394_24715.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3394_24715.FStar_TypeChecker_Common.comp_thunk)
                                                         } in
                                                       let uu____24716 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1 in
                                                       (e, cres6,
                                                         uu____24716))))))))))
      | uu____24717 -> failwith "Impossible"
and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Common.guard_t))
  =
  fun _top_level ->
    fun env ->
      fun lbs ->
        let env0 = env in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____24766 = FStar_Options.ml_ish () in
          if uu____24766
          then FStar_Pervasives_Native.None
          else
            (let lbtyp0 = lbtyp in
             let uu____24779 = FStar_Syntax_Util.abs_formals lbdef in
             match uu____24779 with
             | (actuals, body, body_lc) ->
                 let actuals1 =
                   let uu____24802 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____24802 actuals in
                 let nactuals = FStar_List.length actuals1 in
                 let uu____24810 =
                   FStar_TypeChecker_Normalize.get_n_binders env nactuals
                     lbtyp in
                 (match uu____24810 with
                  | (formals, c) ->
                      (if
                         (FStar_List.isEmpty formals) ||
                           (FStar_List.isEmpty actuals1)
                       then
                         (let uu____24836 =
                            let uu____24841 =
                              let uu____24842 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              let uu____24843 =
                                FStar_Syntax_Print.term_to_string lbtyp in
                              FStar_Util.format2
                                "Only function literals with arrow types can be defined recursively; got %s : %s"
                                uu____24842 uu____24843 in
                            (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                              uu____24841) in
                          FStar_Errors.raise_error uu____24836
                            lbtyp.FStar_Syntax_Syntax.pos)
                       else ();
                       (let nformals = FStar_List.length formals in
                        let uu____24846 =
                          let uu____24847 =
                            FStar_All.pipe_right
                              (FStar_Syntax_Util.comp_effect_name c)
                              (FStar_TypeChecker_Env.lookup_effect_quals env) in
                          FStar_All.pipe_right uu____24847
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect) in
                        if uu____24846
                        then
                          let uu____24860 =
                            let uu____24865 =
                              FStar_Syntax_Util.abs actuals1 body body_lc in
                            (nformals, uu____24865) in
                          FStar_Pervasives_Native.Some uu____24860
                        else FStar_Pervasives_Native.None)))) in
        let uu____24875 =
          FStar_List.fold_left
            (fun uu____24909 ->
               fun lb ->
                 match uu____24909 with
                 | (lbs1, env1, g_acc) ->
                     let uu____24934 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____24934 with
                      | (univ_vars, t, check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let uu____24954 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars in
                               let uu____24971 =
                                 let uu____24978 =
                                   let uu____24979 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____24979 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3434_24990 = env01 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3434_24990.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3434_24990.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3434_24990.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3434_24990.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3434_24990.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3434_24990.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3434_24990.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3434_24990.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3434_24990.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3434_24990.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3434_24990.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3434_24990.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3434_24990.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3434_24990.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3434_24990.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3434_24990.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___3434_24990.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3434_24990.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3434_24990.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3434_24990.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3434_24990.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3434_24990.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3434_24990.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3434_24990.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3434_24990.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3434_24990.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3434_24990.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3434_24990.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3434_24990.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3434_24990.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3434_24990.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3434_24990.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3434_24990.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3434_24990.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3434_24990.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3434_24990.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3434_24990.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3434_24990.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3434_24990.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3434_24990.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3434_24990.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3434_24990.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3434_24990.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3434_24990.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3434_24990.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___3434_24990.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }) t uu____24978 "" in
                               match uu____24971 with
                               | (t1, uu____24998, g) ->
                                   let uu____25000 =
                                     let uu____25001 =
                                       let uu____25002 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2) in
                                       FStar_All.pipe_right uu____25002
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2) in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____25001 in
                                   let uu____25003 = norm env01 t1 in
                                   (uu____25000, uu____25003)) in
                          (match uu____24954 with
                           | (g, t1) ->
                               let uu____25022 =
                                 let uu____25027 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1 in
                                 match uu____25027 with
                                 | FStar_Pervasives_Native.Some (arity, def)
                                     ->
                                     let lb1 =
                                       let uu___3447_25045 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3447_25045.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3447_25045.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = def;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3447_25045.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3447_25045.FStar_Syntax_Syntax.lbpos)
                                       } in
                                     let env3 =
                                       let uu___3450_25047 = env2 in
                                       {
                                         FStar_TypeChecker_Env.solver =
                                           (uu___3450_25047.FStar_TypeChecker_Env.solver);
                                         FStar_TypeChecker_Env.range =
                                           (uu___3450_25047.FStar_TypeChecker_Env.range);
                                         FStar_TypeChecker_Env.curmodule =
                                           (uu___3450_25047.FStar_TypeChecker_Env.curmodule);
                                         FStar_TypeChecker_Env.gamma =
                                           (uu___3450_25047.FStar_TypeChecker_Env.gamma);
                                         FStar_TypeChecker_Env.gamma_sig =
                                           (uu___3450_25047.FStar_TypeChecker_Env.gamma_sig);
                                         FStar_TypeChecker_Env.gamma_cache =
                                           (uu___3450_25047.FStar_TypeChecker_Env.gamma_cache);
                                         FStar_TypeChecker_Env.modules =
                                           (uu___3450_25047.FStar_TypeChecker_Env.modules);
                                         FStar_TypeChecker_Env.expected_typ =
                                           (uu___3450_25047.FStar_TypeChecker_Env.expected_typ);
                                         FStar_TypeChecker_Env.sigtab =
                                           (uu___3450_25047.FStar_TypeChecker_Env.sigtab);
                                         FStar_TypeChecker_Env.attrtab =
                                           (uu___3450_25047.FStar_TypeChecker_Env.attrtab);
                                         FStar_TypeChecker_Env.instantiate_imp
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.instantiate_imp);
                                         FStar_TypeChecker_Env.effects =
                                           (uu___3450_25047.FStar_TypeChecker_Env.effects);
                                         FStar_TypeChecker_Env.generalize =
                                           (uu___3450_25047.FStar_TypeChecker_Env.generalize);
                                         FStar_TypeChecker_Env.letrecs =
                                           (((lb1.FStar_Syntax_Syntax.lbname),
                                              arity, t1, univ_vars) ::
                                           (env2.FStar_TypeChecker_Env.letrecs));
                                         FStar_TypeChecker_Env.top_level =
                                           (uu___3450_25047.FStar_TypeChecker_Env.top_level);
                                         FStar_TypeChecker_Env.check_uvars =
                                           (uu___3450_25047.FStar_TypeChecker_Env.check_uvars);
                                         FStar_TypeChecker_Env.use_eq =
                                           (uu___3450_25047.FStar_TypeChecker_Env.use_eq);
                                         FStar_TypeChecker_Env.use_eq_strict
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.use_eq_strict);
                                         FStar_TypeChecker_Env.is_iface =
                                           (uu___3450_25047.FStar_TypeChecker_Env.is_iface);
                                         FStar_TypeChecker_Env.admit =
                                           (uu___3450_25047.FStar_TypeChecker_Env.admit);
                                         FStar_TypeChecker_Env.lax =
                                           (uu___3450_25047.FStar_TypeChecker_Env.lax);
                                         FStar_TypeChecker_Env.lax_universes
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.lax_universes);
                                         FStar_TypeChecker_Env.phase1 =
                                           (uu___3450_25047.FStar_TypeChecker_Env.phase1);
                                         FStar_TypeChecker_Env.failhard =
                                           (uu___3450_25047.FStar_TypeChecker_Env.failhard);
                                         FStar_TypeChecker_Env.nosynth =
                                           (uu___3450_25047.FStar_TypeChecker_Env.nosynth);
                                         FStar_TypeChecker_Env.uvar_subtyping
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.uvar_subtyping);
                                         FStar_TypeChecker_Env.tc_term =
                                           (uu___3450_25047.FStar_TypeChecker_Env.tc_term);
                                         FStar_TypeChecker_Env.type_of =
                                           (uu___3450_25047.FStar_TypeChecker_Env.type_of);
                                         FStar_TypeChecker_Env.universe_of =
                                           (uu___3450_25047.FStar_TypeChecker_Env.universe_of);
                                         FStar_TypeChecker_Env.check_type_of
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.check_type_of);
                                         FStar_TypeChecker_Env.use_bv_sorts =
                                           (uu___3450_25047.FStar_TypeChecker_Env.use_bv_sorts);
                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.qtbl_name_and_index);
                                         FStar_TypeChecker_Env.normalized_eff_names
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.normalized_eff_names);
                                         FStar_TypeChecker_Env.fv_delta_depths
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.fv_delta_depths);
                                         FStar_TypeChecker_Env.proof_ns =
                                           (uu___3450_25047.FStar_TypeChecker_Env.proof_ns);
                                         FStar_TypeChecker_Env.synth_hook =
                                           (uu___3450_25047.FStar_TypeChecker_Env.synth_hook);
                                         FStar_TypeChecker_Env.try_solve_implicits_hook
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                         FStar_TypeChecker_Env.splice =
                                           (uu___3450_25047.FStar_TypeChecker_Env.splice);
                                         FStar_TypeChecker_Env.mpreprocess =
                                           (uu___3450_25047.FStar_TypeChecker_Env.mpreprocess);
                                         FStar_TypeChecker_Env.postprocess =
                                           (uu___3450_25047.FStar_TypeChecker_Env.postprocess);
                                         FStar_TypeChecker_Env.identifier_info
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.identifier_info);
                                         FStar_TypeChecker_Env.tc_hooks =
                                           (uu___3450_25047.FStar_TypeChecker_Env.tc_hooks);
                                         FStar_TypeChecker_Env.dsenv =
                                           (uu___3450_25047.FStar_TypeChecker_Env.dsenv);
                                         FStar_TypeChecker_Env.nbe =
                                           (uu___3450_25047.FStar_TypeChecker_Env.nbe);
                                         FStar_TypeChecker_Env.strict_args_tab
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.strict_args_tab);
                                         FStar_TypeChecker_Env.erasable_types_tab
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.erasable_types_tab);
                                         FStar_TypeChecker_Env.enable_defer_to_tac
                                           =
                                           (uu___3450_25047.FStar_TypeChecker_Env.enable_defer_to_tac)
                                       } in
                                     (lb1, env3)
                                 | FStar_Pervasives_Native.None ->
                                     let lb1 =
                                       let uu___3454_25061 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3454_25061.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3454_25061.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3454_25061.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3454_25061.FStar_Syntax_Syntax.lbpos)
                                       } in
                                     let uu____25062 =
                                       FStar_TypeChecker_Env.push_let_binding
                                         env2 lb1.FStar_Syntax_Syntax.lbname
                                         (univ_vars, t1) in
                                     (lb1, uu____25062) in
                               (match uu____25022 with
                                | (lb1, env3) -> ((lb1 :: lbs1), env3, g)))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs in
        match uu____24875 with
        | (lbs1, env1, g) -> ((FStar_List.rev lbs1), env1, g)
and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun lbs ->
      let uu____25102 =
        let uu____25111 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb ->
                  let uu____25137 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____25137 with
                  | (bs, t, lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____25167 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____25167
                       | uu____25172 ->
                           let arity =
                             let uu____25175 =
                               FStar_TypeChecker_Env.get_letrec_arity env
                                 lb.FStar_Syntax_Syntax.lbname in
                             match uu____25175 with
                             | FStar_Pervasives_Native.Some n -> n
                             | FStar_Pervasives_Native.None ->
                                 FStar_List.length bs in
                           let uu____25185 = FStar_List.splitAt arity bs in
                           (match uu____25185 with
                            | (bs0, bs1) ->
                                let def =
                                  if FStar_List.isEmpty bs1
                                  then FStar_Syntax_Util.abs bs0 t lcomp
                                  else
                                    (let inner =
                                       FStar_Syntax_Util.abs bs1 t lcomp in
                                     let inner1 =
                                       FStar_Syntax_Subst.close bs0 inner in
                                     let bs01 =
                                       FStar_Syntax_Subst.close_binders bs0 in
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_abs
                                          (bs01, inner1,
                                            FStar_Pervasives_Native.None))
                                       inner1.FStar_Syntax_Syntax.pos) in
                                let lb1 =
                                  let uu___3486_25280 = lb in
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      (uu___3486_25280.FStar_Syntax_Syntax.lbname);
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___3486_25280.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp =
                                      (uu___3486_25280.FStar_Syntax_Syntax.lbtyp);
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___3486_25280.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___3486_25280.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___3486_25280.FStar_Syntax_Syntax.lbpos)
                                  } in
                                let uu____25281 =
                                  let uu____25288 =
                                    FStar_TypeChecker_Env.set_expected_typ
                                      env lb1.FStar_Syntax_Syntax.lbtyp in
                                  tc_tot_or_gtot_term uu____25288
                                    lb1.FStar_Syntax_Syntax.lbdef in
                                (match uu____25281 with
                                 | (e, c, g) ->
                                     ((let uu____25297 =
                                         let uu____25298 =
                                           FStar_TypeChecker_Common.is_total_lcomp
                                             c in
                                         Prims.op_Negation uu____25298 in
                                       if uu____25297
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
                                           lb1.FStar_Syntax_Syntax.lbpos in
                                       (lb2, g)))))))) in
        FStar_All.pipe_right uu____25111 FStar_List.unzip in
      match uu____25102 with
      | (lbs1, gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs
              FStar_TypeChecker_Env.trivial_guard in
          (lbs1, g_lbs)
and (check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names *
          FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t *
          Prims.bool))
  =
  fun top_level ->
    fun env ->
      fun lb ->
        let uu____25347 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____25347 with
        | (env1, uu____25365) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____25373 = check_lbtyp top_level env lb in
            (match uu____25373 with
             | (topt, wf_annot, univ_vars, univ_opening, env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____25417 =
                     tc_maybe_toplevel_term
                       (let uu___3517_25426 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3517_25426.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3517_25426.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3517_25426.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3517_25426.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3517_25426.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3517_25426.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3517_25426.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3517_25426.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3517_25426.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3517_25426.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3517_25426.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3517_25426.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3517_25426.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3517_25426.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3517_25426.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3517_25426.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___3517_25426.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3517_25426.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3517_25426.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3517_25426.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3517_25426.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3517_25426.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3517_25426.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3517_25426.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3517_25426.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3517_25426.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3517_25426.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3517_25426.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3517_25426.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3517_25426.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3517_25426.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3517_25426.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3517_25426.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3517_25426.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3517_25426.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3517_25426.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3517_25426.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3517_25426.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3517_25426.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3517_25426.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3517_25426.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3517_25426.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3517_25426.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3517_25426.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3517_25426.FStar_TypeChecker_Env.erasable_types_tab);
                          FStar_TypeChecker_Env.enable_defer_to_tac =
                            (uu___3517_25426.FStar_TypeChecker_Env.enable_defer_to_tac)
                        }) e11 in
                   match uu____25417 with
                   | (e12, c1, g1) ->
                       let uu____25440 =
                         let uu____25445 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____25450 ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____25445 e12 c1 wf_annot in
                       (match uu____25440 with
                        | (c11, guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f in
                            ((let uu____25465 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____25465
                              then
                                let uu____25466 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____25467 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11 in
                                let uu____25468 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____25466 uu____25467 uu____25468
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
  fun top_level ->
    fun env ->
      fun lb ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____25502 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____25502 with
             | (univ_opening, univ_vars) ->
                 let uu____25535 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars,
                   univ_opening, uu____25535))
        | uu____25540 ->
            let uu____25541 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____25541 with
             | (univ_opening, univ_vars) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____25590 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars,
                     univ_opening, uu____25590)
                 else
                   (let uu____25596 = FStar_Syntax_Util.type_u () in
                    match uu____25596 with
                    | (k, uu____25616) ->
                        let uu____25617 =
                          tc_check_tot_or_gtot_term env1 t1 k "" in
                        (match uu____25617 with
                         | (t2, uu____25639, g) ->
                             ((let uu____25642 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____25642
                               then
                                 let uu____25643 =
                                   let uu____25644 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____25644 in
                                 let uu____25645 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____25643 uu____25645
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____25648 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars, univ_opening, uu____25648))))))
and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env ->
    fun uu____25654 ->
      match uu____25654 with
      | (x, imp) ->
          let uu____25681 = FStar_Syntax_Util.type_u () in
          (match uu____25681 with
           | (tu, u) ->
               ((let uu____25703 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____25703
                 then
                   let uu____25704 = FStar_Syntax_Print.bv_to_string x in
                   let uu____25705 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____25706 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____25704 uu____25705 uu____25706
                 else ());
                (let uu____25708 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu "" in
                 match uu____25708 with
                 | (t, uu____25730, g) ->
                     let uu____25732 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau_or_attr) ->
                           (match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let uu____25755 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau in
                                (match uu____25755 with
                                 | (tau1, uu____25769, g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                               tau1))), g1))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let uu____25776 =
                                  tc_check_tot_or_gtot_term env attr
                                    FStar_Syntax_Syntax.t_unit "" in
                                (match uu____25776 with
                                 | (attr1, uu____25790, g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                               attr1))),
                                       FStar_TypeChecker_Env.trivial_guard)))
                       | uu____25794 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard) in
                     (match uu____25732 with
                      | (imp1, g') ->
                          let x1 =
                            ((let uu___3587_25829 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3587_25829.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3587_25829.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1) in
                          ((let uu____25831 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High in
                            if uu____25831
                            then
                              let uu____25832 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1) in
                              let uu____25835 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____25832
                                uu____25835
                            else ());
                           (let uu____25837 = push_binding env x1 in
                            (x1, uu____25837, g, u)))))))
and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env ->
    fun bs ->
      (let uu____25849 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
       if uu____25849
       then
         let uu____25850 = FStar_Syntax_Print.binders_to_string ", " bs in
         FStar_Util.print1 "Checking binders %s\n" uu____25850
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____25959 = tc_binder env1 b in
             (match uu____25959 with
              | (b1, env', g, u) ->
                  let uu____26008 = aux env' bs2 in
                  (match uu____26008 with
                   | (bs3, env'1, g', us) ->
                       let uu____26069 =
                         let uu____26070 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g' in
                         FStar_TypeChecker_Env.conj_guard g uu____26070 in
                       ((b1 :: bs3), env'1, uu____26069, (u :: us)))) in
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
  fun en ->
    fun pats ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____26178 ->
             fun uu____26179 ->
               match (uu____26178, uu____26179) with
               | ((t, imp), (args1, g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____26271 = tc_term en1 t in
                     match uu____26271 with
                     | (t1, uu____26291, g') ->
                         let uu____26293 =
                           FStar_TypeChecker_Env.conj_guard g g' in
                         (((t1, imp) :: args1), uu____26293)))) args
          ([], FStar_TypeChecker_Env.trivial_guard) in
      FStar_List.fold_right
        (fun p ->
           fun uu____26347 ->
             match uu____26347 with
             | (pats1, g) ->
                 let uu____26374 = tc_args en p in
                 (match uu____26374 with
                  | (args, g') ->
                      let uu____26387 = FStar_TypeChecker_Env.conj_guard g g' in
                      ((args :: pats1), uu____26387))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)
and (tc_tot_or_gtot_term' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      Prims.string ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun msg ->
        let uu____26401 = tc_maybe_toplevel_term env e in
        match uu____26401 with
        | (e1, c, g) ->
            let uu____26417 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c in
            if uu____26417
            then (e1, c, g)
            else
              (let g1 =
                 FStar_TypeChecker_Rel.solve_deferred_constraints env g in
               let uu____26426 = FStar_TypeChecker_Common.lcomp_comp c in
               match uu____26426 with
               | (c1, g_c) ->
                   let c2 = norm_c env c1 in
                   let uu____26440 =
                     let uu____26445 =
                       FStar_TypeChecker_Util.is_pure_effect env
                         (FStar_Syntax_Util.comp_effect_name c2) in
                     if uu____26445
                     then
                       let uu____26450 =
                         FStar_Syntax_Syntax.mk_Total
                           (FStar_Syntax_Util.comp_result c2) in
                       (uu____26450, false)
                     else
                       (let uu____26452 =
                          FStar_Syntax_Syntax.mk_GTotal
                            (FStar_Syntax_Util.comp_result c2) in
                        (uu____26452, true)) in
                   (match uu____26440 with
                    | (target_comp, allow_ghost) ->
                        let uu____26461 =
                          FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                        (match uu____26461 with
                         | FStar_Pervasives_Native.Some g' ->
                             let uu____26471 =
                               FStar_TypeChecker_Common.lcomp_of_comp
                                 target_comp in
                             let uu____26472 =
                               let uu____26473 =
                                 FStar_TypeChecker_Env.conj_guard g_c g' in
                               FStar_TypeChecker_Env.conj_guard g1
                                 uu____26473 in
                             (e1, uu____26471, uu____26472)
                         | uu____26474 ->
                             if allow_ghost
                             then
                               let uu____26483 =
                                 FStar_TypeChecker_Err.expected_ghost_expression
                                   e1 c2 msg in
                               FStar_Errors.raise_error uu____26483
                                 e1.FStar_Syntax_Syntax.pos
                             else
                               (let uu____26495 =
                                  FStar_TypeChecker_Err.expected_pure_expression
                                    e1 c2 msg in
                                FStar_Errors.raise_error uu____26495
                                  e1.FStar_Syntax_Syntax.pos))))
and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  = fun env -> fun e -> tc_tot_or_gtot_term' env e ""
and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        Prims.string ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun t ->
        fun msg ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env t in
          tc_tot_or_gtot_term' env1 e msg
and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env ->
    fun t ->
      let uu____26521 = tc_tot_or_gtot_term env t in
      match uu____26521 with
      | (t1, c, g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      fun k ->
        let uu____26551 = tc_check_tot_or_gtot_term env t k "" in
        match uu____26551 with
        | (t1, uu____26559, g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      (let uu____26579 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____26579
       then
         let uu____26580 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____26580
       else ());
      (let env1 =
         let uu___3683_26583 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3683_26583.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3683_26583.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3683_26583.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3683_26583.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3683_26583.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3683_26583.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3683_26583.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3683_26583.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3683_26583.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3683_26583.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3683_26583.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3683_26583.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3683_26583.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3683_26583.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3683_26583.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___3683_26583.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___3683_26583.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3683_26583.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3683_26583.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3683_26583.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3683_26583.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3683_26583.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3683_26583.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3683_26583.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3683_26583.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3683_26583.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3683_26583.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3683_26583.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3683_26583.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3683_26583.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3683_26583.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3683_26583.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3683_26583.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3683_26583.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3683_26583.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3683_26583.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3683_26583.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3683_26583.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3683_26583.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3683_26583.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3683_26583.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3683_26583.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3683_26583.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3683_26583.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___3683_26583.FStar_TypeChecker_Env.enable_defer_to_tac)
         } in
       let uu____26592 =
         try
           (fun uu___3687_26606 ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1, msg, uu____26627) ->
             let uu____26628 = FStar_TypeChecker_Env.get_range env1 in
             FStar_Errors.raise_error (e1, msg) uu____26628 in
       match uu____26592 with
       | (t, c, g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c in
           let uu____26645 = FStar_TypeChecker_Common.is_total_lcomp c1 in
           if uu____26645
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____26653 =
                let uu____26658 =
                  let uu____26659 = FStar_Syntax_Print.term_to_string e in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____26659 in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____26658) in
              let uu____26660 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____26653 uu____26660))
let level_of_type_fail :
  'uuuuuu26675 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'uuuuuu26675
  =
  fun env ->
    fun e ->
      fun t ->
        let uu____26691 =
          let uu____26696 =
            let uu____26697 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____26697 t in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____26696) in
        let uu____26698 = FStar_TypeChecker_Env.get_range env in
        FStar_Errors.raise_error uu____26691 uu____26698
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      fun t ->
        let rec aux retry t1 =
          let uu____26729 =
            let uu____26730 = FStar_Syntax_Util.unrefine t1 in
            uu____26730.FStar_Syntax_Syntax.n in
          match uu____26729 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____26734 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1 in
                aux false t2
              else
                (let uu____26737 = FStar_Syntax_Util.type_u () in
                 match uu____26737 with
                 | (t_u, u) ->
                     let env1 =
                       let uu___3719_26745 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3719_26745.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3719_26745.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3719_26745.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3719_26745.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3719_26745.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3719_26745.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3719_26745.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3719_26745.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3719_26745.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3719_26745.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3719_26745.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3719_26745.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3719_26745.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3719_26745.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3719_26745.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3719_26745.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3719_26745.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3719_26745.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3719_26745.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3719_26745.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3719_26745.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3719_26745.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3719_26745.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3719_26745.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3719_26745.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3719_26745.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3719_26745.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3719_26745.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3719_26745.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3719_26745.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3719_26745.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3719_26745.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3719_26745.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3719_26745.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3719_26745.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3719_26745.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3719_26745.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3719_26745.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3719_26745.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3719_26745.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3719_26745.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3719_26745.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3719_26745.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3719_26745.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3719_26745.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3719_26745.FStar_TypeChecker_Env.enable_defer_to_tac)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____26749 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____26749
                       | uu____26750 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u)) in
        aux true t
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun e ->
      let uu____26765 =
        let uu____26766 = FStar_Syntax_Subst.compress e in
        uu____26766.FStar_Syntax_Syntax.n in
      match uu____26765 with
      | FStar_Syntax_Syntax.Tm_bvar uu____26769 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____26770 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____26785 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs, t, uu____26801) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t, uu____26845) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____26852 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____26852 with | ((uu____26861, t), uu____26863) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____26869 = FStar_Syntax_Util.unfold_lazy i in
          universe_of_aux env uu____26869
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____26872, (FStar_Util.Inl t, uu____26874), uu____26875) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____26922, (FStar_Util.Inr c, uu____26924), uu____26925) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____26973 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____26982;
             FStar_Syntax_Syntax.vars = uu____26983;_},
           us)
          ->
          let uu____26989 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____26989 with
           | ((us', t), uu____27000) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____27006 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____27006)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____27024 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____27025 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x, uu____27033) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____27060 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____27060 with
           | (bs1, c1) ->
               let us =
                 FStar_List.map
                   (fun uu____27080 ->
                      match uu____27080 with
                      | (b, uu____27088) ->
                          let uu____27093 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____27093) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____27098 = universe_of_aux env res in
                 level_of_type env res uu____27098 in
               let u_c =
                 FStar_All.pipe_right c1
                   (FStar_TypeChecker_Util.universe_of_comp env u_res) in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us)) in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd, args) ->
          let rec type_of_head retry hd1 args1 =
            let hd2 = FStar_Syntax_Subst.compress hd1 in
            match hd2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____27206 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____27221 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____27250 ->
                let uu____27251 = universe_of_aux env hd2 in
                (uu____27251, args1)
            | FStar_Syntax_Syntax.Tm_name uu____27262 ->
                let uu____27263 = universe_of_aux env hd2 in
                (uu____27263, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____27274 ->
                let uu____27287 = universe_of_aux env hd2 in
                (uu____27287, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____27298 ->
                let uu____27305 = universe_of_aux env hd2 in
                (uu____27305, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____27316 ->
                let uu____27343 = universe_of_aux env hd2 in
                (uu____27343, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____27354 ->
                let uu____27361 = universe_of_aux env hd2 in
                (uu____27361, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____27372 ->
                let uu____27373 = universe_of_aux env hd2 in
                (uu____27373, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____27384 ->
                let uu____27399 = universe_of_aux env hd2 in
                (uu____27399, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____27410 ->
                let uu____27417 = universe_of_aux env hd2 in
                (uu____27417, args1)
            | FStar_Syntax_Syntax.Tm_type uu____27428 ->
                let uu____27429 = universe_of_aux env hd2 in
                (uu____27429, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____27440, hd3::uu____27442) ->
                let uu____27507 = FStar_Syntax_Subst.open_branch hd3 in
                (match uu____27507 with
                 | (uu____27522, uu____27523, hd4) ->
                     let uu____27541 = FStar_Syntax_Util.head_and_args hd4 in
                     (match uu____27541 with
                      | (hd5, args') ->
                          type_of_head retry hd5
                            (FStar_List.append args' args1)))
            | uu____27606 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e in
                let uu____27608 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____27608 with
                 | (hd3, args2) -> type_of_head false hd3 args2)
            | uu____27665 ->
                let uu____27666 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____27666 with
                 | (env1, uu____27688) ->
                     let env2 =
                       let uu___3880_27694 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3880_27694.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3880_27694.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3880_27694.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3880_27694.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3880_27694.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3880_27694.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3880_27694.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3880_27694.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3880_27694.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3880_27694.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3880_27694.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3880_27694.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3880_27694.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3880_27694.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3880_27694.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3880_27694.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3880_27694.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3880_27694.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3880_27694.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3880_27694.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3880_27694.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3880_27694.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3880_27694.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3880_27694.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3880_27694.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3880_27694.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3880_27694.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3880_27694.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3880_27694.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3880_27694.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3880_27694.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3880_27694.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3880_27694.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3880_27694.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3880_27694.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3880_27694.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3880_27694.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3880_27694.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3880_27694.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3880_27694.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3880_27694.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3880_27694.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3880_27694.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3880_27694.FStar_TypeChecker_Env.enable_defer_to_tac)
                       } in
                     ((let uu____27696 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____27696
                       then
                         let uu____27697 =
                           let uu____27698 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____27698 in
                         let uu____27699 =
                           FStar_Syntax_Print.term_to_string hd2 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____27697 uu____27699
                       else ());
                      (let uu____27701 = tc_term env2 hd2 in
                       match uu____27701 with
                       | (uu____27722,
                          { FStar_TypeChecker_Common.eff_name = uu____27723;
                            FStar_TypeChecker_Common.res_typ = t;
                            FStar_TypeChecker_Common.cflags = uu____27725;
                            FStar_TypeChecker_Common.comp_thunk = uu____27726;_},
                          g) ->
                           ((let uu____27744 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____27744
                               (fun uu____27745 -> ()));
                            (t, args1))))) in
          let uu____27756 = type_of_head true hd args in
          (match uu____27756 with
           | (t, args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t in
               let uu____27794 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____27794 with
                | (bs, res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst res1
                    else
                      (let uu____27820 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____27820)))
      | FStar_Syntax_Syntax.Tm_match (uu____27821, hd::uu____27823) ->
          let uu____27888 = FStar_Syntax_Subst.open_branch hd in
          (match uu____27888 with
           | (uu____27889, uu____27890, hd1) -> universe_of_aux env hd1)
      | FStar_Syntax_Syntax.Tm_match (uu____27908, []) ->
          level_of_type_fail env e "empty match cases"
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      (let uu____27954 = FStar_TypeChecker_Env.debug env FStar_Options.High in
       if uu____27954
       then
         let uu____27955 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Calling universe_of_aux with %s\n" uu____27955
       else ());
      (let r = universe_of_aux env e in
       (let uu____27959 = FStar_TypeChecker_Env.debug env FStar_Options.High in
        if uu____27959
        then
          let uu____27960 = FStar_Syntax_Print.term_to_string r in
          FStar_Util.print1 "Got result from universe_of_aux = %s\n"
            uu____27960
        else ());
       level_of_type env e r)
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env0 ->
    fun tps ->
      let uu____27984 = tc_binders env0 tps in
      match uu____27984 with
      | (tps1, env, g, us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env0 g; (tps1, env, us))
let rec (type_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let mk_tm_type u =
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          t.FStar_Syntax_Syntax.pos in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____28041 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____28058 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____28063 = FStar_Syntax_Util.unfold_lazy i in
          type_of_well_typed_term env uu____28063
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____28065 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____28065
            (fun uu____28079 ->
               match uu____28079 with
               | (t2, uu____28087) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____28089;
             FStar_Syntax_Syntax.vars = uu____28090;_},
           us)
          ->
          let uu____28096 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____28096
            (fun uu____28110 ->
               match uu____28110 with
               | (t2, uu____28118) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____28119) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____28121 = tc_constant env t1.FStar_Syntax_Syntax.pos sc in
          FStar_Pervasives_Native.Some uu____28121
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____28123 = mk_tm_type (FStar_Syntax_Syntax.U_succ u) in
          FStar_Pervasives_Native.Some uu____28123
      | FStar_Syntax_Syntax.Tm_abs
          (bs, body, FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____28128;_})
          ->
          let mk_comp =
            let uu____28172 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid in
            if uu____28172
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____28200 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid in
               if uu____28200
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None) in
          FStar_Util.bind_opt mk_comp
            (fun f ->
               let uu____28267 = universe_of_well_typed_term env tbody in
               FStar_Util.bind_opt uu____28267
                 (fun u ->
                    let uu____28275 =
                      let uu____28278 =
                        let uu____28279 =
                          let uu____28294 =
                            f tbody (FStar_Pervasives_Native.Some u) in
                          (bs, uu____28294) in
                        FStar_Syntax_Syntax.Tm_arrow uu____28279 in
                      FStar_Syntax_Syntax.mk uu____28278
                        t1.FStar_Syntax_Syntax.pos in
                    FStar_Pervasives_Native.Some uu____28275))
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____28331 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____28331 with
           | (bs1, c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____28390 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1) in
                     FStar_Util.bind_opt uu____28390
                       (fun uc ->
                          let uu____28398 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us)) in
                          FStar_Pervasives_Native.Some uu____28398)
                 | (x, imp)::bs3 ->
                     let uu____28424 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort in
                     FStar_Util.bind_opt uu____28424
                       (fun u_x ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x in
                          aux env2 (u_x :: us) bs3) in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____28433 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x, uu____28453) ->
          let uu____28458 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort in
          FStar_Util.bind_opt uu____28458
            (fun u_x ->
               let uu____28466 = mk_tm_type u_x in
               FStar_Pervasives_Native.Some uu____28466)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____28471;
             FStar_Syntax_Syntax.vars = uu____28472;_},
           a::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____28551 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____28551 with
           | (unary_op, uu____28571) ->
               let head =
                 let uu____28599 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____28599 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____28647;
             FStar_Syntax_Syntax.vars = uu____28648;_},
           a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____28744 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____28744 with
           | (unary_op, uu____28764) ->
               let head =
                 let uu____28792 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   uu____28792 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____28848;
             FStar_Syntax_Syntax.vars = uu____28849;_},
           uu____28850::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____28889;
             FStar_Syntax_Syntax.vars = uu____28890;_},
           (t2, uu____28892)::uu____28893::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd, args) ->
          let t_hd = type_of_well_typed_term env hd in
          let rec aux t_hd1 =
            let uu____28989 =
              let uu____28990 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1 in
              uu____28990.FStar_Syntax_Syntax.n in
            match uu____28989 with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let n_args = FStar_List.length args in
                let n_bs = FStar_List.length bs in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____29062 = FStar_Util.first_N n_args bs in
                    match uu____29062 with
                    | (bs1, rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            t_hd1.FStar_Syntax_Syntax.pos in
                        let uu____29150 =
                          let uu____29155 = FStar_Syntax_Syntax.mk_Total t2 in
                          FStar_Syntax_Subst.open_comp bs1 uu____29155 in
                        (match uu____29150 with
                         | (bs2, c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____29207 = FStar_Syntax_Subst.open_comp bs c in
                       match uu____29207 with
                       | (bs1, c1) ->
                           let uu____29228 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1 in
                           if uu____29228
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____29306 ->
                     match uu____29306 with
                     | (bs1, t2) ->
                         let subst =
                           FStar_List.map2
                             (fun b ->
                                fun a ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args in
                         let uu____29382 = FStar_Syntax_Subst.subst subst t2 in
                         FStar_Pervasives_Native.Some uu____29382)
            | FStar_Syntax_Syntax.Tm_refine (x, uu____29384) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____29390, uu____29391)
                -> aux t2
            | uu____29432 -> FStar_Pervasives_Native.None in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29433, (FStar_Util.Inl t2, uu____29435), uu____29436) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29483, (FStar_Util.Inr c, uu____29485), uu____29486) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____29551 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
          FStar_Pervasives_Native.Some uu____29551
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____29559) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____29564 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____29587 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____29600 ->
          FStar_Pervasives_Native.None
and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let uu____29611 = type_of_well_typed_term env t in
      match uu____29611 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____29617;
            FStar_Syntax_Syntax.vars = uu____29618;_}
          -> FStar_Pervasives_Native.Some u
      | uu____29621 -> FStar_Pervasives_Native.None
let (check_type_of_well_typed_term' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total ->
    fun env ->
      fun t ->
        fun k ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k in
          let env2 =
            let uu___4164_29646 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4164_29646.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4164_29646.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4164_29646.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4164_29646.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4164_29646.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4164_29646.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4164_29646.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4164_29646.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4164_29646.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4164_29646.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4164_29646.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4164_29646.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4164_29646.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4164_29646.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4164_29646.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4164_29646.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4164_29646.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4164_29646.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4164_29646.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4164_29646.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4164_29646.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4164_29646.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4164_29646.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4164_29646.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4164_29646.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4164_29646.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4164_29646.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4164_29646.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4164_29646.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4164_29646.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4164_29646.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4164_29646.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4164_29646.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4164_29646.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4164_29646.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4164_29646.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4164_29646.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4164_29646.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4164_29646.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4164_29646.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4164_29646.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4164_29646.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4164_29646.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4164_29646.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4164_29646.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4164_29646.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let slow_check uu____29652 =
            if must_total
            then
              let uu____29653 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____29653 with | (uu____29660, uu____29661, g) -> g
            else
              (let uu____29664 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____29664 with | (uu____29671, uu____29672, g) -> g) in
          let uu____29674 = type_of_well_typed_term env2 t in
          match uu____29674 with
          | FStar_Pervasives_Native.None -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____29679 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits") in
                if uu____29679
                then
                  let uu____29680 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                  let uu____29681 = FStar_Syntax_Print.term_to_string t in
                  let uu____29682 = FStar_Syntax_Print.term_to_string k' in
                  let uu____29683 = FStar_Syntax_Print.term_to_string k in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____29680 uu____29681 uu____29682 uu____29683
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k in
                (let uu____29689 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits") in
                 if uu____29689
                 then
                   let uu____29690 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                   let uu____29691 = FStar_Syntax_Print.term_to_string t in
                   let uu____29692 = FStar_Syntax_Print.term_to_string k' in
                   let uu____29693 = FStar_Syntax_Print.term_to_string k in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____29690
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____29691 uu____29692 uu____29693
                 else ());
                (match g with
                 | FStar_Pervasives_Native.None -> slow_check ()
                 | FStar_Pervasives_Native.Some g1 -> g1)))
let (check_type_of_well_typed_term :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total ->
    fun env ->
      fun t ->
        fun k ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k in
          let env2 =
            let uu___4195_29719 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4195_29719.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4195_29719.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4195_29719.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4195_29719.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4195_29719.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4195_29719.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4195_29719.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4195_29719.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4195_29719.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4195_29719.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4195_29719.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4195_29719.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4195_29719.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4195_29719.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4195_29719.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4195_29719.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4195_29719.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4195_29719.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4195_29719.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4195_29719.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4195_29719.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4195_29719.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4195_29719.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4195_29719.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4195_29719.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4195_29719.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4195_29719.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4195_29719.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4195_29719.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4195_29719.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4195_29719.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4195_29719.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4195_29719.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4195_29719.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4195_29719.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4195_29719.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4195_29719.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4195_29719.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4195_29719.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4195_29719.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4195_29719.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4195_29719.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4195_29719.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4195_29719.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4195_29719.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4195_29719.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let slow_check uu____29725 =
            if must_total
            then
              let uu____29726 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____29726 with | (uu____29733, uu____29734, g) -> g
            else
              (let uu____29737 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____29737 with | (uu____29744, uu____29745, g) -> g) in
          let uu____29747 =
            let uu____29748 = FStar_Options.__temp_fast_implicits () in
            FStar_All.pipe_left Prims.op_Negation uu____29748 in
          if uu____29747
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k