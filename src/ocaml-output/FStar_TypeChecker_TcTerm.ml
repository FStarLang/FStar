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
      (let uu____3840 = FStar_TypeChecker_Env.debug env FStar_Options.Medium in
       if uu____3840
       then
         let uu____3841 =
           let uu____3842 = FStar_TypeChecker_Env.get_range env in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3842 in
         let uu____3843 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1 in
         let uu____3844 = FStar_Syntax_Print.term_to_string e in
         let uu____3845 =
           let uu____3846 = FStar_Syntax_Subst.compress e in
           FStar_Syntax_Print.tag_of_term uu____3846 in
         let uu____3847 =
           let uu____3848 = FStar_TypeChecker_Env.expected_typ env in
           match uu____3848 with
           | FStar_Pervasives_Native.None -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____3841 uu____3843 uu____3844 uu____3845 uu____3847
       else ());
      (let uu____3853 =
         FStar_Util.record_time
           (fun uu____3871 ->
              tc_maybe_toplevel_term
                (let uu___502_3874 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___502_3874.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___502_3874.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___502_3874.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___502_3874.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___502_3874.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___502_3874.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___502_3874.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___502_3874.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___502_3874.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___502_3874.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___502_3874.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___502_3874.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___502_3874.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___502_3874.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___502_3874.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___502_3874.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___502_3874.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___502_3874.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___502_3874.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___502_3874.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___502_3874.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___502_3874.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___502_3874.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___502_3874.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___502_3874.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___502_3874.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___502_3874.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___502_3874.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___502_3874.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___502_3874.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___502_3874.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___502_3874.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___502_3874.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___502_3874.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___502_3874.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___502_3874.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___502_3874.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___502_3874.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___502_3874.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___502_3874.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___502_3874.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___502_3874.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___502_3874.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___502_3874.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___502_3874.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___502_3874.FStar_TypeChecker_Env.enable_defer_to_tac)
                 }) e) in
       match uu____3853 with
       | (r, ms) ->
           ((let uu____3896 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____3896
             then
               ((let uu____3898 =
                   let uu____3899 = FStar_TypeChecker_Env.get_range env in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3899 in
                 let uu____3900 = FStar_Syntax_Print.term_to_string e in
                 let uu____3901 =
                   let uu____3902 = FStar_Syntax_Subst.compress e in
                   FStar_Syntax_Print.tag_of_term uu____3902 in
                 let uu____3903 = FStar_Util.string_of_int ms in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3898 uu____3900 uu____3901 uu____3903);
                (let uu____3904 = r in
                 match uu____3904 with
                 | (e1, lc, uu____3913) ->
                     let uu____3914 =
                       let uu____3915 = FStar_TypeChecker_Env.get_range env in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3915 in
                     let uu____3916 = FStar_Syntax_Print.term_to_string e1 in
                     let uu____3917 =
                       FStar_TypeChecker_Common.lcomp_to_string lc in
                     let uu____3918 =
                       let uu____3919 = FStar_Syntax_Subst.compress e1 in
                       FStar_Syntax_Print.tag_of_term uu____3919 in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____3914 uu____3916 uu____3917 uu____3918))
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
      (let uu____3933 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
       if uu____3933
       then
         let uu____3934 =
           let uu____3935 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3935 in
         let uu____3936 = FStar_Syntax_Print.tag_of_term top in
         let uu____3937 = FStar_Syntax_Print.term_to_string top in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3934 uu____3936
           uu____3937
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3945 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3966 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3973 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3986 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3987 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3988 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3989 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3990 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4009 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4024 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4031 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt, qi) ->
           let projl uu___2_4047 =
             match uu___2_4047 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4053 -> failwith "projl fail" in
           let non_trivial_antiquotes qi1 =
             let is_name t =
               let uu____4066 =
                 let uu____4067 = FStar_Syntax_Subst.compress t in
                 uu____4067.FStar_Syntax_Syntax.n in
               match uu____4066 with
               | FStar_Syntax_Syntax.Tm_name uu____4070 -> true
               | uu____4071 -> false in
             FStar_Util.for_some
               (fun uu____4080 ->
                  match uu____4080 with
                  | (uu____4085, t) ->
                      let uu____4087 = is_name t in
                      Prims.op_Negation uu____4087)
               qi1.FStar_Syntax_Syntax.antiquotes in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static when non_trivial_antiquotes qi
                ->
                let e0 = e in
                let newbvs =
                  FStar_List.map
                    (fun uu____4105 ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs in
                let lbs =
                  FStar_List.map
                    (fun uu____4148 ->
                       match uu____4148 with
                       | ((bv, t), bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z in
                let qi1 =
                  let uu___575_4177 = qi in
                  let uu____4178 =
                    FStar_List.map
                      (fun uu____4206 ->
                         match uu____4206 with
                         | ((bv, uu____4222), bv') ->
                             let uu____4234 =
                               FStar_Syntax_Syntax.bv_to_name bv' in
                             (bv, uu____4234)) z in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___575_4177.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4178
                  } in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    top.FStar_Syntax_Syntax.pos in
                let e1 =
                  FStar_List.fold_left
                    (fun t ->
                       fun lb ->
                         let uu____4246 =
                           let uu____4247 =
                             let uu____4260 =
                               let uu____4263 =
                                 let uu____4264 =
                                   let uu____4271 =
                                     projl lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Syntax_Syntax.mk_binder uu____4271 in
                                 [uu____4264] in
                               FStar_Syntax_Subst.close uu____4263 t in
                             ((false, [lb]), uu____4260) in
                           FStar_Syntax_Syntax.Tm_let uu____4247 in
                         FStar_Syntax_Syntax.mk uu____4246
                           top.FStar_Syntax_Syntax.pos) nq lbs in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term in
                let uu____4304 =
                  FStar_List.fold_right
                    (fun uu____4340 ->
                       fun uu____4341 ->
                         match (uu____4340, uu____4341) with
                         | ((bv, tm), (aqs_rev, guard)) ->
                             let uu____4410 = tc_term env_tm tm in
                             (match uu____4410 with
                              | (tm1, uu____4428, g) ->
                                  let uu____4430 =
                                    FStar_TypeChecker_Env.conj_guard g guard in
                                  (((bv, tm1) :: aqs_rev), uu____4430))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard) in
                (match uu____4304 with
                 | (aqs_rev, guard) ->
                     let qi1 =
                       let uu___603_4472 = qi in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___603_4472.FStar_Syntax_Syntax.qkind);
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
                let uu____4483 =
                  FStar_TypeChecker_Env.clear_expected_typ env1 in
                (match uu____4483 with
                 | (env', uu____4497) ->
                     let uu____4502 =
                       tc_term
                         (let uu___612_4511 = env' in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___612_4511.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___612_4511.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___612_4511.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___612_4511.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___612_4511.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___612_4511.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___612_4511.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___612_4511.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___612_4511.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___612_4511.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___612_4511.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___612_4511.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___612_4511.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___612_4511.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___612_4511.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___612_4511.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___612_4511.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___612_4511.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___612_4511.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___612_4511.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___612_4511.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___612_4511.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___612_4511.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___612_4511.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___612_4511.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___612_4511.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___612_4511.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___612_4511.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___612_4511.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___612_4511.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___612_4511.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___612_4511.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___612_4511.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___612_4511.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___612_4511.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___612_4511.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___612_4511.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___612_4511.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___612_4511.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___612_4511.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___612_4511.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___612_4511.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___612_4511.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___612_4511.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___612_4511.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___612_4511.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) qt in
                     (match uu____4502 with
                      | (qt1, uu____4519, uu____4520) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4526 =
                            let uu____4533 =
                              let uu____4538 =
                                FStar_TypeChecker_Common.lcomp_of_comp c in
                              FStar_Util.Inr uu____4538 in
                            value_check_expected_typ env1 top uu____4533
                              FStar_TypeChecker_Env.trivial_guard in
                          (match uu____4526 with
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
           { FStar_Syntax_Syntax.blob = uu____4555;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4556;
             FStar_Syntax_Syntax.ltyp = uu____4557;
             FStar_Syntax_Syntax.rng = uu____4558;_}
           ->
           let uu____4569 = FStar_Syntax_Util.unlazy top in
           tc_term env1 uu____4569
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat))
           ->
           let uu____4576 = tc_tot_or_gtot_term env1 e1 in
           (match uu____4576 with
            | (e2, c, g) ->
                let g1 =
                  let uu___642_4593 = g in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___642_4593.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___642_4593.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___642_4593.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___642_4593.FStar_TypeChecker_Common.implicits)
                  } in
                let uu____4594 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    top.FStar_Syntax_Syntax.pos in
                (uu____4594, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_pattern (names, pats)) ->
           let uu____4636 = FStar_Syntax_Util.type_u () in
           (match uu____4636 with
            | (t, u) ->
                let uu____4649 = tc_check_tot_or_gtot_term env1 e1 t "" in
                (match uu____4649 with
                 | (e2, c, g) ->
                     let uu____4665 =
                       let uu____4682 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____4682 with
                       | (env2, uu____4706) -> tc_smt_pats env2 pats in
                     (match uu____4665 with
                      | (pats1, g') ->
                          let g'1 =
                            let uu___665_4744 = g' in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred_to_tac =
                                (uu___665_4744.FStar_TypeChecker_Common.deferred_to_tac);
                              FStar_TypeChecker_Common.deferred =
                                (uu___665_4744.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___665_4744.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___665_4744.FStar_TypeChecker_Common.implicits)
                            } in
                          let uu____4745 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names, pats1))))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4764 =
                            FStar_TypeChecker_Env.conj_guard g g'1 in
                          (uu____4745, c, uu____4764))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence))
           ->
           let uu____4770 =
             let uu____4771 = FStar_Syntax_Subst.compress e1 in
             uu____4771.FStar_Syntax_Syntax.n in
           (match uu____4770 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4780,
                  { FStar_Syntax_Syntax.lbname = x;
                    FStar_Syntax_Syntax.lbunivs = uu____4782;
                    FStar_Syntax_Syntax.lbtyp = uu____4783;
                    FStar_Syntax_Syntax.lbeff = uu____4784;
                    FStar_Syntax_Syntax.lbdef = e11;
                    FStar_Syntax_Syntax.lbattrs = uu____4786;
                    FStar_Syntax_Syntax.lbpos = uu____4787;_}::[]),
                 e2)
                ->
                let uu____4815 =
                  let uu____4822 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____4822 e11 in
                (match uu____4815 with
                 | (e12, c1, g1) ->
                     let uu____4832 = tc_term env1 e2 in
                     (match uu____4832 with
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
                            let uu____4856 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name in
                            if uu____4856
                            then [FStar_Syntax_Util.inline_let_attr]
                            else [] in
                          let e3 =
                            let uu____4863 =
                              let uu____4864 =
                                let uu____4877 =
                                  let uu____4884 =
                                    let uu____4887 =
                                      FStar_Syntax_Syntax.mk_lb
                                        (x, [],
                                          (c.FStar_TypeChecker_Common.eff_name),
                                          FStar_Syntax_Syntax.t_unit, e13,
                                          attrs,
                                          (e13.FStar_Syntax_Syntax.pos)) in
                                    [uu____4887] in
                                  (false, uu____4884) in
                                (uu____4877, e22) in
                              FStar_Syntax_Syntax.Tm_let uu____4864 in
                            FStar_Syntax_Syntax.mk uu____4863
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
                          let uu____4908 =
                            FStar_TypeChecker_Env.conj_guard g1 g2 in
                          (e5, c, uu____4908)))
            | uu____4909 ->
                let uu____4910 = tc_term env1 e1 in
                (match uu____4910 with
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
           (e1, FStar_Syntax_Syntax.Meta_monadic uu____4932) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_monadic_lift uu____4944) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1, m) ->
           let uu____4963 = tc_term env1 e1 in
           (match uu____4963 with
            | (e2, c, g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (asc, FStar_Pervasives_Native.Some tac), labopt) ->
           let uu____5036 =
             tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
               env1 tac in
           (match uu____5036 with
            | (tac1, uu____5050, g_tac) ->
                let t' =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_ascribed
                       (e1, (asc, FStar_Pervasives_Native.None), labopt))
                    top.FStar_Syntax_Syntax.pos in
                let uu____5089 = tc_term env1 t' in
                (match uu____5089 with
                 | (t'1, c, g) ->
                     let t'2 =
                       let uu____5106 =
                         let uu____5107 = FStar_Syntax_Subst.compress t'1 in
                         uu____5107.FStar_Syntax_Syntax.n in
                       match uu____5106 with
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (e2, (asc1, FStar_Pervasives_Native.None),
                            labopt1)
                           ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_ascribed
                                (e2,
                                  (asc1, (FStar_Pervasives_Native.Some tac1)),
                                  labopt1)) t'1.FStar_Syntax_Syntax.pos
                       | uu____5193 -> failwith "impossible" in
                     let g1 =
                       wrap_guard_with_tactic_opt
                         (FStar_Pervasives_Native.Some tac1) g in
                     let uu____5195 =
                       FStar_TypeChecker_Env.conj_guard g1 g_tac in
                     (t'2, c, uu____5195)))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____5196,
            (FStar_Util.Inr expected_c, FStar_Pervasives_Native.None),
            uu____5198)
           when
           let uu____5243 = FStar_All.pipe_right top is_comp_ascribed_reflect in
           FStar_All.pipe_right uu____5243 FStar_Util.is_some ->
           let uu____5274 =
             let uu____5283 =
               FStar_All.pipe_right top is_comp_ascribed_reflect in
             FStar_All.pipe_right uu____5283 FStar_Util.must in
           (match uu____5274 with
            | (effect_lid, e1, aqual) ->
                let uu____5335 =
                  FStar_TypeChecker_Env.clear_expected_typ env1 in
                (match uu____5335 with
                 | (env0, uu____5349) ->
                     let uu____5354 = tc_comp env0 expected_c in
                     (match uu____5354 with
                      | (expected_c1, uu____5368, g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1 in
                          ((let uu____5372 =
                              let uu____5373 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name in
                              Prims.op_Negation uu____5373 in
                            if uu____5372
                            then
                              let uu____5374 =
                                let uu____5379 =
                                  let uu____5380 =
                                    FStar_Ident.string_of_lid effect_lid in
                                  let uu____5381 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5380 uu____5381 in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5379) in
                              FStar_Errors.raise_error uu____5374
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5384 =
                              let uu____5385 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid in
                              Prims.op_Negation uu____5385 in
                            if uu____5384
                            then
                              let uu____5386 =
                                let uu____5391 =
                                  let uu____5392 =
                                    FStar_Ident.string_of_lid effect_lid in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5392 in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5391) in
                              FStar_Errors.raise_error uu____5386
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd in
                            let repr =
                              let uu____5398 =
                                let uu____5401 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5401 u_c in
                              FStar_All.pipe_right uu____5398 FStar_Util.must in
                            let e2 =
                              let uu____5407 =
                                let uu____5408 =
                                  let uu____5435 =
                                    let uu____5452 =
                                      let uu____5461 =
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          (FStar_Pervasives_Native.Some u_c) in
                                      FStar_Util.Inr uu____5461 in
                                    (uu____5452,
                                      FStar_Pervasives_Native.None) in
                                  (e1, uu____5435,
                                    FStar_Pervasives_Native.None) in
                                FStar_Syntax_Syntax.Tm_ascribed uu____5408 in
                              FStar_Syntax_Syntax.mk uu____5407
                                e1.FStar_Syntax_Syntax.pos in
                            (let uu____5503 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme in
                             if uu____5503
                             then
                               let uu____5504 =
                                 FStar_Syntax_Print.term_to_string e2 in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5504
                             else ());
                            (let uu____5506 = tc_tot_or_gtot_term env0 e2 in
                             match uu____5506 with
                             | (e3, uu____5520, g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3 in
                                 ((let uu____5524 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme in
                                   if uu____5524
                                   then
                                     let uu____5525 =
                                       FStar_Syntax_Print.term_to_string e4 in
                                     let uu____5526 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5525 uu____5526
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
                                     let uu____5570 =
                                       let uu____5571 =
                                         let uu____5598 =
                                           let uu____5601 =
                                             FStar_All.pipe_right expected_c1
                                               FStar_Syntax_Util.comp_effect_name in
                                           FStar_All.pipe_right uu____5601
                                             (fun uu____5606 ->
                                                FStar_Pervasives_Native.Some
                                                  uu____5606) in
                                         (tm1,
                                           ((FStar_Util.Inr expected_c1),
                                             FStar_Pervasives_Native.None),
                                           uu____5598) in
                                       FStar_Syntax_Syntax.Tm_ascribed
                                         uu____5571 in
                                     FStar_Syntax_Syntax.mk uu____5570 r in
                                   let uu____5645 =
                                     let uu____5652 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     comp_check_expected_typ env1 top1
                                       uu____5652 in
                                   match uu____5645 with
                                   | (top2, c, g_env) ->
                                       let uu____5662 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env] in
                                       (top2, c, uu____5662)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inr expected_c, FStar_Pervasives_Native.None),
            uu____5665)
           ->
           let uu____5710 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____5710 with
            | (env0, uu____5724) ->
                let uu____5729 = tc_comp env0 expected_c in
                (match uu____5729 with
                 | (expected_c1, uu____5743, g) ->
                     let uu____5745 =
                       let uu____5752 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0) in
                       tc_term uu____5752 e1 in
                     (match uu____5745 with
                      | (e2, c', g') ->
                          let uu____5762 =
                            let uu____5773 =
                              FStar_TypeChecker_Common.lcomp_comp c' in
                            match uu____5773 with
                            | (c'1, g_c') ->
                                let uu____5790 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1) in
                                (match uu____5790 with
                                 | (e3, expected_c2, g'') ->
                                     let uu____5810 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g'' in
                                     (e3, expected_c2, uu____5810)) in
                          (match uu____5762 with
                           | (e3, expected_c2, g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inr expected_c2),
                                          FStar_Pervasives_Native.None),
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Util.comp_effect_name
                                              expected_c2))))
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_TypeChecker_Common.lcomp_of_comp
                                   expected_c2 in
                               let f =
                                 let uu____5875 =
                                   FStar_TypeChecker_Env.conj_guard g' g'' in
                                 FStar_TypeChecker_Env.conj_guard g
                                   uu____5875 in
                               let uu____5876 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____5876 with
                                | (e5, c, f2) ->
                                    let uu____5892 =
                                      FStar_TypeChecker_Env.conj_guard f f2 in
                                    (e5, c, uu____5892))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inl t, FStar_Pervasives_Native.None), uu____5895)
           ->
           let uu____5940 = FStar_Syntax_Util.type_u () in
           (match uu____5940 with
            | (k, u) ->
                let uu____5953 = tc_check_tot_or_gtot_term env1 t k "" in
                (match uu____5953 with
                 | (t1, uu____5967, f) ->
                     let uu____5969 =
                       let uu____5976 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____5976 e1 in
                     (match uu____5969 with
                      | (e2, c, g) ->
                          let uu____5986 =
                            let uu____5991 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____5996 ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____5991 e2 c f in
                          (match uu____5986 with
                           | (c1, f1) ->
                               let uu____6005 =
                                 let uu____6012 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_TypeChecker_Common.eff_name))))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____6012 c1 in
                               (match uu____6005 with
                                | (e3, c2, f2) ->
                                    let uu____6060 =
                                      let uu____6061 =
                                        FStar_TypeChecker_Env.conj_guard g f2 in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____6061 in
                                    (e3, c2, uu____6060))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____6062;
              FStar_Syntax_Syntax.vars = uu____6063;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6142 = FStar_Syntax_Util.head_and_args top in
           (match uu____6142 with
            | (unary_op, uu____6166) ->
                let head =
                  let uu____6194 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6194 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____6242;
              FStar_Syntax_Syntax.vars = uu____6243;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6322 = FStar_Syntax_Util.head_and_args top in
           (match uu____6322 with
            | (unary_op, uu____6346) ->
                let head =
                  let uu____6374 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6374 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6422);
              FStar_Syntax_Syntax.pos = uu____6423;
              FStar_Syntax_Syntax.vars = uu____6424;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6503 = FStar_Syntax_Util.head_and_args top in
           (match uu____6503 with
            | (unary_op, uu____6527) ->
                let head =
                  let uu____6555 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6555 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____6603;
              FStar_Syntax_Syntax.vars = uu____6604;_},
            a1::a2::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6700 = FStar_Syntax_Util.head_and_args top in
           (match uu____6700 with
            | (unary_op, uu____6724) ->
                let head =
                  let uu____6752 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    uu____6752 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____6808;
              FStar_Syntax_Syntax.vars = uu____6809;_},
            (e1, FStar_Pervasives_Native.None)::[])
           ->
           let uu____6847 =
             let uu____6854 =
               let uu____6855 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6855 in
             tc_term uu____6854 e1 in
           (match uu____6847 with
            | (e2, c, g) ->
                let uu____6879 = FStar_Syntax_Util.head_and_args top in
                (match uu____6879 with
                 | (head, uu____6903) ->
                     let uu____6928 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head, [(e2, FStar_Pervasives_Native.None)]))
                         top.FStar_Syntax_Syntax.pos in
                     let uu____6961 =
                       let uu____6962 =
                         let uu____6963 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____6963 in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____6962 in
                     (uu____6928, uu____6961, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____6964;
              FStar_Syntax_Syntax.vars = uu____6965;_},
            (t, FStar_Pervasives_Native.None)::(r,
                                                FStar_Pervasives_Native.None)::[])
           ->
           let uu____7018 = FStar_Syntax_Util.head_and_args top in
           (match uu____7018 with
            | (head, uu____7042) ->
                let env' =
                  let uu____7068 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____7068 in
                let uu____7069 = tc_term env' r in
                (match uu____7069 with
                 | (er, uu____7083, gr) ->
                     let uu____7085 = tc_term env1 t in
                     (match uu____7085 with
                      | (t1, tt, gt) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt in
                          let uu____7102 =
                            let uu____7103 =
                              let uu____7104 = FStar_Syntax_Syntax.as_arg t1 in
                              let uu____7113 =
                                let uu____7124 = FStar_Syntax_Syntax.as_arg r in
                                [uu____7124] in
                              uu____7104 :: uu____7113 in
                            FStar_Syntax_Syntax.mk_Tm_app head uu____7103
                              top.FStar_Syntax_Syntax.pos in
                          (uu____7102, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____7157;
              FStar_Syntax_Syntax.vars = uu____7158;_},
            uu____7159)
           ->
           let uu____7184 =
             let uu____7189 =
               let uu____7190 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____7190 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7189) in
           FStar_Errors.raise_error uu____7184 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____7197;
              FStar_Syntax_Syntax.vars = uu____7198;_},
            uu____7199)
           ->
           let uu____7224 =
             let uu____7229 =
               let uu____7230 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____7230 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7229) in
           FStar_Errors.raise_error uu____7224 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____7237;
              FStar_Syntax_Syntax.vars = uu____7238;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7281 = FStar_TypeChecker_Env.clear_expected_typ env1 in
             match uu____7281 with
             | (env0, uu____7295) ->
                 let uu____7300 = tc_term env0 e1 in
                 (match uu____7300 with
                  | (e2, c, g) ->
                      let uu____7316 = FStar_Syntax_Util.head_and_args top in
                      (match uu____7316 with
                       | (reify_op, uu____7340) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ in
                           let uu____7366 =
                             FStar_TypeChecker_Common.lcomp_comp c in
                           (match uu____7366 with
                            | (c1, g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1 in
                                ((let uu____7381 =
                                    let uu____7382 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef in
                                    Prims.op_Negation uu____7382 in
                                  if uu____7381
                                  then
                                    let uu____7383 =
                                      let uu____7388 =
                                        let uu____7389 =
                                          FStar_Ident.string_of_lid ef in
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          uu____7389 in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7388) in
                                    FStar_Errors.raise_error uu____7383
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
                                    let uu____7428 =
                                      FStar_TypeChecker_Env.is_total_effect
                                        env1 ef in
                                    if uu____7428
                                    then
                                      let uu____7429 =
                                        FStar_Syntax_Syntax.mk_Total repr in
                                      FStar_All.pipe_right uu____7429
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
                                       let uu____7440 =
                                         FStar_Syntax_Syntax.mk_Comp ct in
                                       FStar_All.pipe_right uu____7440
                                         FStar_TypeChecker_Common.lcomp_of_comp) in
                                  let uu____7441 =
                                    comp_check_expected_typ env1 e3 c2 in
                                  match uu____7441 with
                                  | (e4, c3, g') ->
                                      let uu____7457 =
                                        let uu____7458 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g' in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7458 in
                                      (e4, c3, uu____7457))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7460;
              FStar_Syntax_Syntax.vars = uu____7461;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7505 =
               let uu____7506 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l in
               Prims.op_Negation uu____7506 in
             if uu____7505
             then
               let uu____7507 =
                 let uu____7512 =
                   let uu____7513 = FStar_Ident.string_of_lid l in
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     uu____7513 in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7512) in
               FStar_Errors.raise_error uu____7507 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7515 = FStar_Syntax_Util.head_and_args top in
             match uu____7515 with
             | (reflect_op, uu____7539) ->
                 let uu____7564 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____7564 with
                  | FStar_Pervasives_Native.None ->
                      let uu____7585 =
                        let uu____7590 =
                          let uu____7591 = FStar_Ident.string_of_lid l in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7591 in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7590) in
                      FStar_Errors.raise_error uu____7585
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                      let uu____7610 =
                        FStar_TypeChecker_Env.clear_expected_typ env1 in
                      (match uu____7610 with
                       | (env_no_ex, uu____7624) ->
                           let uu____7629 =
                             let uu____7638 =
                               tc_tot_or_gtot_term env_no_ex e1 in
                             match uu____7638 with
                             | (e2, c, g) ->
                                 ((let uu____7657 =
                                     let uu____7658 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7658 in
                                   if uu____7657
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g)) in
                           (match uu____7629 with
                            | (e2, c_e, g_e) ->
                                let uu____7687 =
                                  let uu____7702 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____7702 with
                                  | (a, u_a) ->
                                      let uu____7723 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a in
                                      (match uu____7723 with
                                       | (a_uvar, uu____7751, g_a) ->
                                           let uu____7765 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar in
                                           (uu____7765, u_a, a_uvar, g_a)) in
                                (match uu____7687 with
                                 | ((expected_repr_typ, g_repr), u_a, a, g_a)
                                     ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ in
                                     let eff_args =
                                       let uu____7807 =
                                         let uu____7808 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ in
                                         uu____7808.FStar_Syntax_Syntax.n in
                                       match uu____7807 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7821, uu____7822::args) ->
                                           args
                                       | uu____7864 ->
                                           let uu____7865 =
                                             let uu____7870 =
                                               let uu____7871 =
                                                 FStar_Ident.string_of_lid l in
                                               let uu____7872 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ in
                                               let uu____7873 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____7871 uu____7872
                                                 uu____7873 in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____7870) in
                                           FStar_Errors.raise_error
                                             uu____7865
                                             top.FStar_Syntax_Syntax.pos in
                                     let c =
                                       let uu____7885 =
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
                                       FStar_All.pipe_right uu____7885
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         top.FStar_Syntax_Syntax.pos in
                                     let uu____7921 =
                                       comp_check_expected_typ env1 e3 c in
                                     (match uu____7921 with
                                      | (e4, c1, g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_TypeChecker_Common.eff_name),
                                                        (c1.FStar_TypeChecker_Common.res_typ)))))
                                              e4.FStar_Syntax_Syntax.pos in
                                          let uu____7944 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g'] in
                                          (e5, c1, uu____7944))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head, (tau, FStar_Pervasives_Native.None)::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7983 = FStar_Syntax_Util.head_and_args top in
           (match uu____7983 with
            | (head1, args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head,
            (uu____8033, FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____8034))::(tau,
                                                          FStar_Pervasives_Native.None)::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8086 = FStar_Syntax_Util.head_and_args top in
           (match uu____8086 with
            | (head1, args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head, args) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8161 =
             match args with
             | (tau, FStar_Pervasives_Native.None)::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau, FStar_Pervasives_Native.None)::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8370 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos in
           (match uu____8161 with
            | (args1, args2) ->
                let t1 = FStar_Syntax_Util.mk_app head args1 in
                let t2 = FStar_Syntax_Util.mk_app t1 args2 in tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head, args) ->
           let env0 = env1 in
           let env2 =
             let uu____8487 =
               let uu____8488 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____8488 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____8487 instantiate_both in
           ((let uu____8504 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____8504
             then
               let uu____8505 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____8506 = FStar_Syntax_Print.term_to_string top in
               let uu____8507 =
                 let uu____8508 = FStar_TypeChecker_Env.expected_typ env0 in
                 FStar_All.pipe_right uu____8508
                   (fun uu___3_8514 ->
                      match uu___3_8514 with
                      | FStar_Pervasives_Native.None -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t) in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8505
                 uu____8506 uu____8507
             else ());
            (let uu____8519 = tc_term (no_inst env2) head in
             match uu____8519 with
             | (head1, chead, g_head) ->
                 let uu____8535 =
                   let uu____8540 = FStar_TypeChecker_Common.lcomp_comp chead in
                   FStar_All.pipe_right uu____8540
                     (fun uu____8557 ->
                        match uu____8557 with
                        | (c, g) ->
                            let uu____8568 =
                              FStar_TypeChecker_Env.conj_guard g_head g in
                            (c, uu____8568)) in
                 (match uu____8535 with
                  | (chead1, g_head1) ->
                      let uu____8577 =
                        let uu____8584 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8586 = FStar_Options.lax () in
                              Prims.op_Negation uu____8586))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head1) in
                        if uu____8584
                        then
                          let uu____8593 =
                            let uu____8600 =
                              FStar_TypeChecker_Env.expected_typ env0 in
                            check_short_circuit_args env2 head1 chead1
                              g_head1 args uu____8600 in
                          match uu____8593 with | (e1, c, g) -> (e1, c, g)
                        else
                          (let uu____8613 =
                             FStar_TypeChecker_Env.expected_typ env0 in
                           check_application_args env2 head1 chead1 g_head1
                             args uu____8613) in
                      (match uu____8577 with
                       | (e1, c, g) ->
                           let uu____8625 =
                             let uu____8632 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c in
                             if uu____8632
                             then
                               let uu____8639 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ in
                               match uu____8639 with
                               | (e2, res_typ, implicits) ->
                                   let uu____8655 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ in
                                   (e2, uu____8655, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard) in
                           (match uu____8625 with
                            | (e2, c1, implicits) ->
                                ((let uu____8667 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme in
                                  if uu____8667
                                  then
                                    let uu____8668 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8668
                                  else ());
                                 (let uu____8670 =
                                    comp_check_expected_typ env0 e2 c1 in
                                  match uu____8670 with
                                  | (e3, c2, g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits in
                                      ((let uu____8689 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme in
                                        if uu____8689
                                        then
                                          let uu____8690 =
                                            FStar_Syntax_Print.term_to_string
                                              e3 in
                                          let uu____8691 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1 in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8690 uu____8691
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8693 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8716;
               FStar_Syntax_Syntax.lbunivs = uu____8717;
               FStar_Syntax_Syntax.lbtyp = uu____8718;
               FStar_Syntax_Syntax.lbeff = uu____8719;
               FStar_Syntax_Syntax.lbdef = uu____8720;
               FStar_Syntax_Syntax.lbattrs = uu____8721;
               FStar_Syntax_Syntax.lbpos = uu____8722;_}::[]),
            uu____8723)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false, uu____8746), uu____8747) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8762;
               FStar_Syntax_Syntax.lbunivs = uu____8763;
               FStar_Syntax_Syntax.lbtyp = uu____8764;
               FStar_Syntax_Syntax.lbeff = uu____8765;
               FStar_Syntax_Syntax.lbdef = uu____8766;
               FStar_Syntax_Syntax.lbattrs = uu____8767;
               FStar_Syntax_Syntax.lbpos = uu____8768;_}::uu____8769),
            uu____8770)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true, uu____8795), uu____8796) ->
           check_inner_let_rec env1 top)
and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      let uu____8819 =
        let uu____8820 = FStar_Syntax_Subst.compress top in
        uu____8820.FStar_Syntax_Syntax.n in
      match uu____8819 with
      | FStar_Syntax_Syntax.Tm_match (e1, eqns) ->
          let uu____8867 = FStar_TypeChecker_Env.clear_expected_typ env in
          (match uu____8867 with
           | (env1, topt) ->
               let env11 = instantiate_both env1 in
               let uu____8887 = tc_term env11 e1 in
               (match uu____8887 with
                | (e11, c1, g1) ->
                    let uu____8903 =
                      let uu____8914 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1 in
                      match uu____8914 with
                      | FStar_Pervasives_Native.Some (e12, c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None -> (e11, c1, eqns) in
                    (match uu____8903 with
                     | (e12, c11, eqns1) ->
                         let eqns2 = eqns1 in
                         let uu____8969 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None ->
                               let uu____8983 = FStar_Syntax_Util.type_u () in
                               (match uu____8983 with
                                | (k, uu____8995) ->
                                    let uu____8996 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k in
                                    (match uu____8996 with
                                     | (res_t, uu____9016, g) ->
                                         let uu____9030 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t in
                                         let uu____9031 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g in
                                         (uu____9030, res_t, uu____9031))) in
                         (match uu____8969 with
                          | (env_branches, res_t, g11) ->
                              ((let uu____9042 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme in
                                if uu____9042
                                then
                                  let uu____9043 =
                                    FStar_Syntax_Print.term_to_string res_t in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____9043
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
                                let uu____9142 =
                                  let uu____9149 =
                                    FStar_List.fold_right
                                      (fun uu____9236 ->
                                         fun uu____9237 ->
                                           match (uu____9236, uu____9237)
                                           with
                                           | ((branch, f, eff_label, cflags,
                                               c, g, erasable_branch),
                                              (caccum, gaccum, erasable)) ->
                                               let uu____9487 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9487,
                                                 (erasable || erasable_branch)))
                                      t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false) in
                                  match uu____9149 with
                                  | (cases, g, erasable) ->
                                      let uu____9588 =
                                        FStar_TypeChecker_Util.bind_cases env
                                          res_t cases guard_x in
                                      (uu____9588, g, erasable) in
                                match uu____9142 with
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
                                        let uu____9604 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9604
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____9741 ->
                                                  match uu____9741 with
                                                  | ((pat, wopt, br),
                                                     uu____9787, eff_label,
                                                     uu____9789, uu____9790,
                                                     uu____9791, uu____9792)
                                                      ->
                                                      let uu____9827 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t in
                                                      (pat, wopt, uu____9827))) in
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
                                      let uu____9894 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name in
                                      if uu____9894
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____9899 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x in
                                           mk_match uu____9899 in
                                         let lb =
                                           let uu____9903 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____9903 e12 []
                                             e12.FStar_Syntax_Syntax.pos in
                                         let e =
                                           let uu____9909 =
                                             let uu____9910 =
                                               let uu____9923 =
                                                 let uu____9926 =
                                                   let uu____9927 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       guard_x in
                                                   [uu____9927] in
                                                 FStar_Syntax_Subst.close
                                                   uu____9926 e_match in
                                               ((false, [lb]), uu____9923) in
                                             FStar_Syntax_Syntax.Tm_let
                                               uu____9910 in
                                           FStar_Syntax_Syntax.mk uu____9909
                                             top.FStar_Syntax_Syntax.pos in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ) in
                                    ((let uu____9957 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme in
                                      if uu____9957
                                      then
                                        let uu____9958 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos in
                                        let uu____9959 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1 in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____9958 uu____9959
                                      else ());
                                     (let uu____9961 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches in
                                      (e, cres1, uu____9961)))))))))
      | uu____9962 ->
          let uu____9963 =
            let uu____9964 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format1 "tc_match called on %s\n" uu____9964 in
          failwith uu____9963
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
          let uu____9987 =
            match args with
            | (tau, FStar_Pervasives_Native.None)::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____10026))::(tau, FStar_Pervasives_Native.None)::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____10066 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng in
          match uu____9987 with
          | (tau, atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None ->
                    let uu____10097 = FStar_TypeChecker_Env.expected_typ env in
                    (match uu____10097 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None ->
                         let uu____10101 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____10101) in
              let uu____10102 =
                let uu____10109 =
                  let uu____10110 =
                    let uu____10111 = FStar_Syntax_Util.type_u () in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____10111 in
                  FStar_TypeChecker_Env.set_expected_typ env uu____10110 in
                tc_term uu____10109 typ in
              (match uu____10102 with
               | (typ1, uu____10127, g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____10130 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau in
                     match uu____10130 with
                     | (tau1, uu____10144, g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1360_10149 = tau1 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1360_10149.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1360_10149.FStar_Syntax_Syntax.vars)
                                }) in
                           (let uu____10151 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac") in
                            if uu____10151
                            then
                              let uu____10152 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print1 "Got %s\n" uu____10152
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10155 =
                              let uu____10156 =
                                FStar_Syntax_Syntax.mk_Total typ1 in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10156 in
                            (t, uu____10155,
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
            let uu___1370_10162 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1370_10162.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1370_10162.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1370_10162.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1370_10162.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1370_10162.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1370_10162.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1370_10162.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1370_10162.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1370_10162.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1370_10162.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1370_10162.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1370_10162.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1370_10162.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1370_10162.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1370_10162.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1370_10162.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1370_10162.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1370_10162.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1370_10162.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1370_10162.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1370_10162.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1370_10162.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1370_10162.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1370_10162.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1370_10162.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1370_10162.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1370_10162.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1370_10162.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1370_10162.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1370_10162.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1370_10162.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1370_10162.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1370_10162.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1370_10162.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1370_10162.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1370_10162.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1370_10162.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1370_10162.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1370_10162.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1370_10162.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1370_10162.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1370_10162.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1370_10162.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1370_10162.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1370_10162.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___1370_10162.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let uu____10163 = FStar_Syntax_Syntax.t_tac_of a b in
          tc_check_tot_or_gtot_term env1 tau uu____10163 ""
and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun topt ->
      match topt with
      | FStar_Pervasives_Native.None ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____10177 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic in
          (match uu____10177 with
           | (tactic1, uu____10191, g) ->
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
        let uu____10244 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____10244 with
        | (e2, t1, implicits) ->
            let tc =
              let uu____10265 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____10265
              then FStar_Util.Inl t1
              else
                (let uu____10271 =
                   let uu____10272 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____10272 in
                 FStar_Util.Inr uu____10271) in
            let is_data_ctor uu___4_10280 =
              match uu___4_10280 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10283) -> true
              | uu____10290 -> false in
            let uu____10293 =
              (is_data_ctor dc) &&
                (let uu____10295 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____10295) in
            if uu____10293
            then
              let uu____10302 =
                let uu____10307 =
                  let uu____10308 =
                    FStar_Ident.string_of_lid v.FStar_Syntax_Syntax.v in
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    uu____10308 in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10307) in
              let uu____10309 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____10302 uu____10309
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10326 =
            let uu____10331 =
              let uu____10332 = FStar_Syntax_Print.term_to_string top in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10332 in
            (FStar_Errors.Error_IllScopedTerm, uu____10331) in
          FStar_Errors.raise_error uu____10326 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____10357 =
            let uu____10362 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
            FStar_Util.Inl uu____10362 in
          value_check_expected_typ env1 e uu____10357
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____10364 =
            let uu____10377 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____10377 with
            | FStar_Pervasives_Native.None ->
                let uu____10392 = FStar_Syntax_Util.type_u () in
                (match uu____10392 with
                 | (k, u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard) in
          (match uu____10364 with
           | (t, uu____10429, g0) ->
               let uu____10443 =
                 let uu____10456 =
                   let uu____10457 = FStar_Range.string_of_range r in
                   Prims.op_Hat "user-provided implicit term at " uu____10457 in
                 FStar_TypeChecker_Util.new_implicit_var uu____10456 r env1 t in
               (match uu____10443 with
                | (e1, uu____10465, g1) ->
                    let uu____10479 =
                      let uu____10480 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____10480
                        FStar_TypeChecker_Common.lcomp_of_comp in
                    let uu____10481 = FStar_TypeChecker_Env.conj_guard g0 g1 in
                    (e1, uu____10479, uu____10481)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10483 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10492 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____10492)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____10483 with
           | (t, rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1436_10505 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1436_10505.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1436_10505.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____10508 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____10508 with
                 | (e2, t1, implicits) ->
                     let tc =
                       let uu____10529 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____10529
                       then FStar_Util.Inl t1
                       else
                         (let uu____10535 =
                            let uu____10536 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____10536 in
                          FStar_Util.Inr uu____10535) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10538;
             FStar_Syntax_Syntax.vars = uu____10539;_},
           uu____10540)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10545 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10545
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10553 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10553
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10561;
             FStar_Syntax_Syntax.vars = uu____10562;_},
           us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____10571 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10571 with
           | ((us', t), range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range in
               (maybe_warn_on_use env1 fv1;
                if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10596 =
                     let uu____10601 =
                       let uu____10602 = FStar_Syntax_Print.fv_to_string fv1 in
                       let uu____10603 =
                         FStar_Util.string_of_int (FStar_List.length us1) in
                       let uu____10604 =
                         FStar_Util.string_of_int (FStar_List.length us') in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10602 uu____10603 uu____10604 in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10601) in
                   let uu____10605 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____10596 uu____10605)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10623 -> failwith "Impossible") us' us1;
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____10626 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____10626 us1 in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_uinst (uu____10627, us) ->
          let uu____10633 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
              "Universe applications are only allowed on top-level identifiers")
            uu____10633
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10641 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10641 with
           | ((us, t), range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range in
               (maybe_warn_on_use env1 fv1;
                (let uu____10666 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____10666
                 then
                   let uu____10667 =
                     let uu____10668 = FStar_Syntax_Syntax.lid_of_fv fv1 in
                     FStar_Syntax_Print.lid_to_string uu____10668 in
                   let uu____10669 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____10670 = FStar_Range.string_of_range range in
                   let uu____10671 = FStar_Range.string_of_use_range range in
                   let uu____10672 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____10667 uu____10669 uu____10670 uu____10671
                     uu____10672
                 else ());
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____10676 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____10676 us in
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
          let uu____10704 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10704 with
           | (bs1, c1) ->
               let env0 = env1 in
               let uu____10718 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____10718 with
                | (env2, uu____10732) ->
                    let uu____10737 = tc_binders env2 bs1 in
                    (match uu____10737 with
                     | (bs2, env3, g, us) ->
                         let uu____10756 = tc_comp env3 c1 in
                         (match uu____10756 with
                          | (c2, uc, f) ->
                              let e1 =
                                let uu___1522_10775 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1522_10775.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1522_10775.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____10786 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____10786 in
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
          let uu____10802 =
            let uu____10807 =
              let uu____10808 = FStar_Syntax_Syntax.mk_binder x in
              [uu____10808] in
            FStar_Syntax_Subst.open_term uu____10807 phi in
          (match uu____10802 with
           | (x1, phi1) ->
               let env0 = env1 in
               let uu____10836 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____10836 with
                | (env2, uu____10850) ->
                    let uu____10855 =
                      let uu____10870 = FStar_List.hd x1 in
                      tc_binder env2 uu____10870 in
                    (match uu____10855 with
                     | (x2, env3, f1, u) ->
                         ((let uu____10906 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____10906
                           then
                             let uu____10907 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____10908 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____10909 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10907 uu____10908 uu____10909
                           else ());
                          (let uu____10913 = FStar_Syntax_Util.type_u () in
                           match uu____10913 with
                           | (t_phi, uu____10925) ->
                               let uu____10926 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                   "refinement formula must be pure or ghost" in
                               (match uu____10926 with
                                | (phi2, uu____10940, f2) ->
                                    let e1 =
                                      let uu___1560_10945 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1560_10945.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1560_10945.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____10954 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10954 in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____10982) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____11009 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
            if uu____11009
            then
              let uu____11010 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1573_11013 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1573_11013.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1573_11013.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____11010
            else ());
           (let uu____11027 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____11027 with
            | (bs2, body1) -> tc_abs env1 top bs2 body1))
      | uu____11040 ->
          let uu____11041 =
            let uu____11042 = FStar_Syntax_Print.term_to_string top in
            let uu____11043 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____11042
              uu____11043 in
          failwith uu____11041
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
          | FStar_Const.Const_bool uu____11054 -> FStar_Syntax_Util.t_bool
          | FStar_Const.Const_int (uu____11055, FStar_Pervasives_Native.None)
              -> FStar_Syntax_Syntax.t_int
          | FStar_Const.Const_int
              (uu____11066, FStar_Pervasives_Native.Some msize) ->
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
          | FStar_Const.Const_string uu____11082 ->
              FStar_Syntax_Syntax.t_string
          | FStar_Const.Const_real uu____11087 -> FStar_Syntax_Syntax.t_real
          | FStar_Const.Const_float uu____11088 ->
              FStar_Syntax_Syntax.t_float
          | FStar_Const.Const_char uu____11089 ->
              let uu____11090 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
              FStar_All.pipe_right uu____11090 FStar_Util.must
          | FStar_Const.Const_effect -> FStar_Syntax_Util.ktype0
          | FStar_Const.Const_range uu____11095 ->
              FStar_Syntax_Syntax.t_range
          | FStar_Const.Const_range_of ->
              let uu____11096 =
                let uu____11101 =
                  let uu____11102 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11102 in
                (FStar_Errors.Fatal_IllTyped, uu____11101) in
              FStar_Errors.raise_error uu____11096 r
          | FStar_Const.Const_set_range_of ->
              let uu____11103 =
                let uu____11108 =
                  let uu____11109 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11109 in
                (FStar_Errors.Fatal_IllTyped, uu____11108) in
              FStar_Errors.raise_error uu____11103 r
          | FStar_Const.Const_reify ->
              let uu____11110 =
                let uu____11115 =
                  let uu____11116 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11116 in
                (FStar_Errors.Fatal_IllTyped, uu____11115) in
              FStar_Errors.raise_error uu____11110 r
          | FStar_Const.Const_reflect uu____11117 ->
              let uu____11118 =
                let uu____11123 =
                  let uu____11124 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11124 in
                (FStar_Errors.Fatal_IllTyped, uu____11123) in
              FStar_Errors.raise_error uu____11118 r
          | uu____11125 ->
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
      | FStar_Syntax_Syntax.Total (t, uu____11142) ->
          let uu____11151 = FStar_Syntax_Util.type_u () in
          (match uu____11151 with
           | (k, u) ->
               let uu____11164 = tc_check_tot_or_gtot_term env t k "" in
               (match uu____11164 with
                | (t1, uu____11178, g) ->
                    let uu____11180 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____11180, u, g)))
      | FStar_Syntax_Syntax.GTotal (t, uu____11182) ->
          let uu____11191 = FStar_Syntax_Util.type_u () in
          (match uu____11191 with
           | (k, u) ->
               let uu____11204 = tc_check_tot_or_gtot_term env t k "" in
               (match uu____11204 with
                | (t1, uu____11218, g) ->
                    let uu____11220 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____11220, u, g)))
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
            let uu____11228 =
              let uu____11229 =
                FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ in
              uu____11229 :: (c1.FStar_Syntax_Syntax.effect_args) in
            FStar_Syntax_Syntax.mk_Tm_app head1 uu____11228
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____11246 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff "" in
          (match uu____11246 with
           | (tc1, uu____11260, f) ->
               let uu____11262 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____11262 with
                | (head2, args) ->
                    let comp_univs =
                      let uu____11312 =
                        let uu____11313 = FStar_Syntax_Subst.compress head2 in
                        uu____11313.FStar_Syntax_Syntax.n in
                      match uu____11312 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11316, us) -> us
                      | uu____11322 -> [] in
                    let uu____11323 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____11323 with
                     | (uu____11346, args1) ->
                         let uu____11372 =
                           let uu____11395 = FStar_List.hd args1 in
                           let uu____11412 = FStar_List.tl args1 in
                           (uu____11395, uu____11412) in
                         (match uu____11372 with
                          | (res, args2) ->
                              let uu____11493 =
                                let uu____11502 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_11530 ->
                                          match uu___5_11530 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____11538 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____11538 with
                                               | (env1, uu____11550) ->
                                                   let uu____11555 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____11555 with
                                                    | (e1, uu____11567, g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard))) in
                                FStar_All.pipe_right uu____11502
                                  FStar_List.unzip in
                              (match uu____11493 with
                               | (flags, guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1703_11608 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1703_11608.FStar_Syntax_Syntax.effect_name);
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
                                   let uu____11614 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards in
                                   (c2, u_c, uu____11614))))))
and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____11624 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____11625 -> u2
        | FStar_Syntax_Syntax.U_zero -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____11637 = aux u3 in
            FStar_Syntax_Syntax.U_succ uu____11637
        | FStar_Syntax_Syntax.U_max us ->
            let uu____11641 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____11641
        | FStar_Syntax_Syntax.U_name x ->
            let uu____11645 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x) in
            if uu____11645
            then u2
            else
              (let uu____11647 =
                 let uu____11648 =
                   let uu____11649 = FStar_Syntax_Print.univ_to_string u2 in
                   Prims.op_Hat uu____11649 " not found" in
                 Prims.op_Hat "Universe variable " uu____11648 in
               failwith uu____11647) in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown ->
             let uu____11651 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____11651 FStar_Pervasives_Native.snd
         | uu____11660 -> aux u)
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
                | uu____11694 ->
                    failwith
                      "Impossible: Can't have a let rec annotation but no expected type");
               (let uu____11705 = tc_binders env bs in
                match uu____11705 with
                | (bs1, envbody, g_env, uu____11735) ->
                    (FStar_Pervasives_Native.None, bs1, [],
                      FStar_Pervasives_Native.None, envbody, body, g_env)))
          | FStar_Pervasives_Native.Some t ->
              let t1 = FStar_Syntax_Subst.compress t in
              let rec as_function_typ norm1 t2 =
                let uu____11779 =
                  let uu____11780 = FStar_Syntax_Subst.compress t2 in
                  uu____11780.FStar_Syntax_Syntax.n in
                match uu____11779 with
                | FStar_Syntax_Syntax.Tm_uvar uu____11803 ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____11825 -> failwith "Impossible");
                     (let uu____11836 = tc_binders env bs in
                      match uu____11836 with
                      | (bs1, envbody, g_env, uu____11868) ->
                          let uu____11869 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody in
                          (match uu____11869 with
                           | (envbody1, uu____11897) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____11908;
                       FStar_Syntax_Syntax.pos = uu____11909;
                       FStar_Syntax_Syntax.vars = uu____11910;_},
                     uu____11911)
                    ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____11957 -> failwith "Impossible");
                     (let uu____11968 = tc_binders env bs in
                      match uu____11968 with
                      | (bs1, envbody, g_env, uu____12000) ->
                          let uu____12001 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody in
                          (match uu____12001 with
                           | (envbody1, uu____12029) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_refine (b, uu____12041) ->
                    let uu____12046 =
                      as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                    (match uu____12046 with
                     | (uu____12087, bs1, bs', copt, env_body, body1, g_env)
                         ->
                         ((FStar_Pervasives_Native.Some t2), bs1, bs', copt,
                           env_body, body1, g_env))
                | FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) ->
                    let uu____12134 =
                      FStar_Syntax_Subst.open_comp bs_expected c_expected in
                    (match uu____12134 with
                     | (bs_expected1, c_expected1) ->
                         let check_actuals_against_formals env1 bs1
                           bs_expected2 body1 =
                           let rec handle_more uu____12269 c_expected2 body2
                             =
                             match uu____12269 with
                             | (env_bs, bs2, more, guard_env, subst) ->
                                 (match more with
                                  | FStar_Pervasives_Native.None ->
                                      let uu____12383 =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2 in
                                      (env_bs, bs2, guard_env, uu____12383,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inr more_bs_expected) ->
                                      let c =
                                        let uu____12400 =
                                          FStar_Syntax_Util.arrow
                                            more_bs_expected c_expected2 in
                                        FStar_Syntax_Syntax.mk_Total
                                          uu____12400 in
                                      let uu____12401 =
                                        FStar_Syntax_Subst.subst_comp subst c in
                                      (env_bs, bs2, guard_env, uu____12401,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inl more_bs) ->
                                      let c =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2 in
                                      let uu____12418 =
                                        (FStar_Options.ml_ish ()) ||
                                          (FStar_Syntax_Util.is_named_tot c) in
                                      if uu____12418
                                      then
                                        let t3 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env_bs
                                            (FStar_Syntax_Util.comp_result c) in
                                        (match t3.FStar_Syntax_Syntax.n with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs_expected3, c_expected3) ->
                                             let uu____12482 =
                                               FStar_Syntax_Subst.open_comp
                                                 bs_expected3 c_expected3 in
                                             (match uu____12482 with
                                              | (bs_expected4, c_expected4)
                                                  ->
                                                  let uu____12509 =
                                                    tc_abs_check_binders
                                                      env_bs more_bs
                                                      bs_expected4 in
                                                  (match uu____12509 with
                                                   | (env_bs_bs', bs', more1,
                                                      guard'_env_bs, subst1)
                                                       ->
                                                       let guard'_env =
                                                         FStar_TypeChecker_Env.close_guard
                                                           env_bs bs2
                                                           guard'_env_bs in
                                                       let uu____12564 =
                                                         let uu____12591 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard_env
                                                             guard'_env in
                                                         (env_bs_bs',
                                                           (FStar_List.append
                                                              bs2 bs'),
                                                           more1,
                                                           uu____12591,
                                                           subst1) in
                                                       handle_more
                                                         uu____12564
                                                         c_expected4 body2))
                                         | uu____12614 ->
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
                           let uu____12642 =
                             tc_abs_check_binders env1 bs1 bs_expected2 in
                           handle_more uu____12642 c_expected1 body1 in
                         let mk_letrec_env envbody bs1 c =
                           let letrecs = guard_letrecs envbody bs1 c in
                           let envbody1 =
                             let uu___1834_12707 = envbody in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1834_12707.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1834_12707.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1834_12707.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1834_12707.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1834_12707.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1834_12707.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1834_12707.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1834_12707.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1834_12707.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1834_12707.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1834_12707.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1834_12707.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1834_12707.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs = [];
                               FStar_TypeChecker_Env.top_level =
                                 (uu___1834_12707.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1834_12707.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___1834_12707.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (uu___1834_12707.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1834_12707.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1834_12707.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1834_12707.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1834_12707.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1834_12707.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1834_12707.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1834_12707.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1834_12707.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1834_12707.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1834_12707.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1834_12707.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1834_12707.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1834_12707.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1834_12707.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1834_12707.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1834_12707.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1834_12707.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1834_12707.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1834_12707.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1834_12707.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1834_12707.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1834_12707.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1834_12707.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1834_12707.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1834_12707.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1834_12707.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1834_12707.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1834_12707.FStar_TypeChecker_Env.erasable_types_tab);
                               FStar_TypeChecker_Env.enable_defer_to_tac =
                                 (uu___1834_12707.FStar_TypeChecker_Env.enable_defer_to_tac)
                             } in
                           let uu____12716 =
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____12782 ->
                                     fun uu____12783 ->
                                       match (uu____12782, uu____12783) with
                                       | ((env1, letrec_binders, g),
                                          (l, t3, u_names)) ->
                                           let uu____12874 =
                                             let uu____12881 =
                                               let uu____12882 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env1 in
                                               FStar_All.pipe_right
                                                 uu____12882
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____12881 t3 in
                                           (match uu____12874 with
                                            | (t4, uu____12906, g') ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env1 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____12919 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___1852_12922
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___1852_12922.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___1852_12922.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____12919 ::
                                                        letrec_binders
                                                  | uu____12923 ->
                                                      letrec_binders in
                                                let uu____12928 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g' in
                                                (env2, lb, uu____12928)))
                                  (envbody1, [],
                                    FStar_TypeChecker_Env.trivial_guard)) in
                           match uu____12716 with
                           | (envbody2, letrec_binders, g) ->
                               let uu____12948 =
                                 FStar_TypeChecker_Env.close_guard envbody2
                                   bs1 g in
                               (envbody2, letrec_binders, uu____12948) in
                         let envbody =
                           let uu___1860_12952 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1860_12952.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1860_12952.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1860_12952.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1860_12952.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1860_12952.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1860_12952.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1860_12952.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1860_12952.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1860_12952.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1860_12952.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1860_12952.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1860_12952.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1860_12952.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs = [];
                             FStar_TypeChecker_Env.top_level =
                               (uu___1860_12952.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1860_12952.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1860_12952.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1860_12952.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1860_12952.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1860_12952.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___1860_12952.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1860_12952.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1860_12952.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1860_12952.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1860_12952.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1860_12952.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1860_12952.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1860_12952.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1860_12952.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1860_12952.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1860_12952.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1860_12952.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1860_12952.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1860_12952.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1860_12952.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1860_12952.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1860_12952.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1860_12952.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1860_12952.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1860_12952.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1860_12952.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1860_12952.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1860_12952.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1860_12952.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1860_12952.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1860_12952.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1860_12952.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let uu____12961 =
                           check_actuals_against_formals envbody bs
                             bs_expected1 body in
                         (match uu____12961 with
                          | (envbody1, bs1, g_env, c, body1) ->
                              let envbody2 =
                                let uu___1869_12998 = envbody1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1869_12998.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1869_12998.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1869_12998.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___1869_12998.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1869_12998.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___1869_12998.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1869_12998.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1869_12998.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1869_12998.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1869_12998.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1869_12998.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1869_12998.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1869_12998.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (env.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1869_12998.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1869_12998.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1869_12998.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1869_12998.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1869_12998.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1869_12998.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1869_12998.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1869_12998.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1869_12998.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1869_12998.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1869_12998.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1869_12998.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1869_12998.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1869_12998.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1869_12998.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1869_12998.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1869_12998.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1869_12998.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1869_12998.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1869_12998.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1869_12998.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1869_12998.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1869_12998.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1869_12998.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1869_12998.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1869_12998.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1869_12998.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1869_12998.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1869_12998.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1869_12998.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1869_12998.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1869_12998.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1869_12998.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____12999 = mk_letrec_env envbody2 bs1 c in
                              (match uu____12999 with
                               | (envbody3, letrecs, g_annots) ->
                                   let envbody4 =
                                     FStar_TypeChecker_Env.set_expected_typ
                                       envbody3
                                       (FStar_Syntax_Util.comp_result c) in
                                   let uu____13036 =
                                     FStar_TypeChecker_Env.conj_guard g_env
                                       g_annots in
                                   ((FStar_Pervasives_Native.Some t2), bs1,
                                     letrecs,
                                     (FStar_Pervasives_Native.Some c),
                                     envbody4, body1, uu____13036))))
                | uu____13043 ->
                    if Prims.op_Negation norm1
                    then
                      let uu____13064 =
                        let uu____13065 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.unfold_whnf env) in
                        FStar_All.pipe_right uu____13065
                          FStar_Syntax_Util.unascribe in
                      as_function_typ true uu____13064
                    else
                      (let uu____13067 =
                         tc_abs_expected_function_typ env bs
                           FStar_Pervasives_Native.None body in
                       match uu____13067 with
                       | (uu____13106, bs1, uu____13108, c_opt, envbody,
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
        let rec aux uu____13181 bs1 bs_expected1 =
          match uu____13181 with
          | (env1, subst) ->
              (match (bs1, bs_expected1) with
               | ([], []) ->
                   (env1, [], FStar_Pervasives_Native.None,
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ((uu____13288, FStar_Pervasives_Native.None)::uu____13289,
                  (hd_e, q)::uu____13292) when
                   FStar_Syntax_Syntax.is_implicit_or_meta q ->
                   let bv =
                     let uu____13344 =
                       let uu____13347 =
                         FStar_Ident.range_of_id
                           hd_e.FStar_Syntax_Syntax.ppname in
                       FStar_Pervasives_Native.Some uu____13347 in
                     let uu____13348 =
                       FStar_Syntax_Subst.subst subst
                         hd_e.FStar_Syntax_Syntax.sort in
                     FStar_Syntax_Syntax.new_bv uu____13344 uu____13348 in
                   aux (env1, subst) ((bv, q) :: bs1) bs_expected1
               | ((hd, imp)::bs2, (hd_expected, imp')::bs_expected2) ->
                   ((let special q1 q2 =
                       match (q1, q2) with
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13441),
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13442)) -> true
                       | (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Equality)) -> true
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____13451),
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13452)) -> true
                       | uu____13457 -> false in
                     let uu____13466 =
                       (Prims.op_Negation (special imp imp')) &&
                         (let uu____13468 =
                            FStar_Syntax_Util.eq_aqual imp imp' in
                          uu____13468 <> FStar_Syntax_Util.Equal) in
                     if uu____13466
                     then
                       let uu____13469 =
                         let uu____13474 =
                           let uu____13475 =
                             FStar_Syntax_Print.bv_to_string hd in
                           FStar_Util.format1
                             "Inconsistent implicit argument annotation on argument %s"
                             uu____13475 in
                         (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                           uu____13474) in
                       let uu____13476 = FStar_Syntax_Syntax.range_of_bv hd in
                       FStar_Errors.raise_error uu____13469 uu____13476
                     else ());
                    (let expected_t =
                       FStar_Syntax_Subst.subst subst
                         hd_expected.FStar_Syntax_Syntax.sort in
                     let uu____13479 =
                       let uu____13486 =
                         let uu____13487 =
                           FStar_Syntax_Util.unmeta
                             hd.FStar_Syntax_Syntax.sort in
                         uu____13487.FStar_Syntax_Syntax.n in
                       match uu____13486 with
                       | FStar_Syntax_Syntax.Tm_unknown ->
                           (expected_t, FStar_TypeChecker_Env.trivial_guard)
                       | uu____13498 ->
                           ((let uu____13500 =
                               FStar_TypeChecker_Env.debug env1
                                 FStar_Options.High in
                             if uu____13500
                             then
                               let uu____13501 =
                                 FStar_Syntax_Print.bv_to_string hd in
                               FStar_Util.print1 "Checking binder %s\n"
                                 uu____13501
                             else ());
                            (let uu____13503 =
                               tc_tot_or_gtot_term env1
                                 hd.FStar_Syntax_Syntax.sort in
                             match uu____13503 with
                             | (t, uu____13517, g1_env) ->
                                 let g2_env =
                                   let uu____13520 =
                                     FStar_TypeChecker_Rel.teq_nosmt env1 t
                                       expected_t in
                                   match uu____13520 with
                                   | FStar_Pervasives_Native.Some g ->
                                       FStar_All.pipe_right g
                                         (FStar_TypeChecker_Rel.resolve_implicits
                                            env1)
                                   | FStar_Pervasives_Native.None ->
                                       let uu____13524 =
                                         FStar_TypeChecker_Rel.get_subtyping_prop
                                           env1 expected_t t in
                                       (match uu____13524 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu____13527 =
                                              FStar_TypeChecker_Err.basic_type_error
                                                env1
                                                FStar_Pervasives_Native.None
                                                expected_t t in
                                            let uu____13532 =
                                              FStar_TypeChecker_Env.get_range
                                                env1 in
                                            FStar_Errors.raise_error
                                              uu____13527 uu____13532
                                        | FStar_Pervasives_Native.Some g_env
                                            ->
                                            FStar_TypeChecker_Util.label_guard
                                              (hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                              "Type annotation on parameter incompatible with the expected type"
                                              g_env) in
                                 let uu____13534 =
                                   FStar_TypeChecker_Env.conj_guard g1_env
                                     g2_env in
                                 (t, uu____13534))) in
                     match uu____13479 with
                     | (t, g_env) ->
                         let hd1 =
                           let uu___1965_13560 = hd in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1965_13560.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1965_13560.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t
                           } in
                         let b = (hd1, imp) in
                         let b_expected = (hd_expected, imp') in
                         let env_b = push_binding env1 b in
                         let subst1 =
                           let uu____13583 =
                             FStar_Syntax_Syntax.bv_to_name hd1 in
                           maybe_extend_subst subst b_expected uu____13583 in
                         let uu____13586 =
                           aux (env_b, subst1) bs2 bs_expected2 in
                         (match uu____13586 with
                          | (env_bs, bs3, rest, g'_env_b, subst2) ->
                              let g'_env =
                                FStar_TypeChecker_Env.close_guard env_bs 
                                  [b] g'_env_b in
                              let uu____13651 =
                                FStar_TypeChecker_Env.conj_guard g_env g'_env in
                              (env_bs, (b :: bs3), rest, uu____13651, subst2))))
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
            let uu____13788 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top in
            FStar_Errors.raise_error uu____13788 top.FStar_Syntax_Syntax.pos in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____13794 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____13794 with
          | (env1, topt) ->
              ((let uu____13814 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____13814
                then
                  let uu____13815 =
                    match topt with
                    | FStar_Pervasives_Native.None -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13815
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13819 =
                  tc_abs_expected_function_typ env1 bs topt body in
                match uu____13819 with
                | (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1,
                   g_env) ->
                    ((let uu____13860 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme in
                      if uu____13860
                      then
                        let uu____13861 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t in
                        let uu____13863 =
                          match c_opt with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t in
                        let uu____13865 =
                          let uu____13866 =
                            FStar_TypeChecker_Env.expected_typ envbody in
                          match uu____13866 with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____13861 uu____13863 uu____13865
                      else ());
                     (let uu____13872 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC") in
                      if uu____13872
                      then
                        let uu____13873 =
                          FStar_Syntax_Print.binders_to_string ", " bs1 in
                        let uu____13874 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13873 uu____13874
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos in
                      let uu____13877 =
                        let uu____13888 =
                          let uu____13895 =
                            (FStar_All.pipe_right c_opt FStar_Util.is_some)
                              &&
                              (let uu____13903 =
                                 let uu____13904 =
                                   FStar_Syntax_Subst.compress body1 in
                                 uu____13904.FStar_Syntax_Syntax.n in
                               match uu____13903 with
                               | FStar_Syntax_Syntax.Tm_app (head, args) when
                                   (FStar_List.length args) = Prims.int_one
                                   ->
                                   let uu____13941 =
                                     let uu____13942 =
                                       FStar_Syntax_Subst.compress head in
                                     uu____13942.FStar_Syntax_Syntax.n in
                                   (match uu____13941 with
                                    | FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reflect
                                        uu____13945) -> true
                                    | uu____13946 -> false)
                               | uu____13947 -> false) in
                          if uu____13895
                          then
                            let uu____13954 =
                              let uu____13955 =
                                FStar_TypeChecker_Env.clear_expected_typ
                                  envbody1 in
                              FStar_All.pipe_right uu____13955
                                FStar_Pervasives_Native.fst in
                            let uu____13970 =
                              let uu____13971 =
                                let uu____13972 =
                                  let uu____13999 =
                                    let uu____14016 =
                                      let uu____14025 =
                                        FStar_All.pipe_right c_opt
                                          FStar_Util.must in
                                      FStar_Util.Inr uu____14025 in
                                    (uu____14016,
                                      FStar_Pervasives_Native.None) in
                                  (body1, uu____13999,
                                    FStar_Pervasives_Native.None) in
                                FStar_Syntax_Syntax.Tm_ascribed uu____13972 in
                              FStar_Syntax_Syntax.mk uu____13971
                                FStar_Range.dummyRange in
                            (uu____13954, uu____13970, false)
                          else
                            (let uu____14075 =
                               let uu____14076 =
                                 let uu____14083 =
                                   let uu____14084 =
                                     FStar_Syntax_Subst.compress body1 in
                                   uu____14084.FStar_Syntax_Syntax.n in
                                 (c_opt, uu____14083) in
                               match uu____14076 with
                               | (FStar_Pervasives_Native.None,
                                  FStar_Syntax_Syntax.Tm_ascribed
                                  (uu____14089,
                                   (FStar_Util.Inr expected_c, uu____14091),
                                   uu____14092)) -> false
                               | uu____14141 -> true in
                             (envbody1, body1, uu____14075)) in
                        match uu____13888 with
                        | (envbody2, body2, should_check_expected_effect) ->
                            let uu____14161 =
                              tc_term
                                (let uu___2050_14170 = envbody2 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2050_14170.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2050_14170.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2050_14170.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2050_14170.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2050_14170.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2050_14170.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2050_14170.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2050_14170.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2050_14170.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2050_14170.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2050_14170.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2050_14170.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2050_14170.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2050_14170.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level = false;
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2050_14170.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___2050_14170.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2050_14170.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2050_14170.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___2050_14170.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2050_14170.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2050_14170.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2050_14170.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2050_14170.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2050_14170.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2050_14170.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2050_14170.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2050_14170.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2050_14170.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2050_14170.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2050_14170.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2050_14170.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2050_14170.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2050_14170.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2050_14170.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___2050_14170.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2050_14170.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___2050_14170.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2050_14170.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2050_14170.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2050_14170.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2050_14170.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2050_14170.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___2050_14170.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___2050_14170.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___2050_14170.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) body2 in
                            (match uu____14161 with
                             | (body3, cbody, guard_body) ->
                                 let guard_body1 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     envbody2 guard_body in
                                 if should_check_expected_effect
                                 then
                                   let uu____14195 =
                                     FStar_TypeChecker_Common.lcomp_comp
                                       cbody in
                                   (match uu____14195 with
                                    | (cbody1, g_lc) ->
                                        let uu____14212 =
                                          check_expected_effect
                                            (let uu___2061_14221 = envbody2 in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 use_eq;
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.lax);
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.phase1);
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___2061_14221.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) c_opt (body3, cbody1) in
                                        (match uu____14212 with
                                         | (body4, cbody2, guard) ->
                                             let uu____14235 =
                                               let uu____14236 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_lc guard in
                                               FStar_TypeChecker_Env.conj_guard
                                                 guard_body1 uu____14236 in
                                             (body4, cbody2, uu____14235)))
                                 else
                                   (let uu____14242 =
                                      FStar_TypeChecker_Common.lcomp_comp
                                        cbody in
                                    match uu____14242 with
                                    | (cbody1, g_lc) ->
                                        let uu____14259 =
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 g_lc in
                                        (body3, cbody1, uu____14259))) in
                      match uu____13877 with
                      | (body2, cbody, guard_body) ->
                          let guard =
                            let uu____14282 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14284 =
                                   FStar_TypeChecker_Env.should_verify env1 in
                                 Prims.op_Negation uu____14284) in
                            if uu____14282
                            then
                              let uu____14285 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env in
                              let uu____14286 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body in
                              FStar_TypeChecker_Env.conj_guard uu____14285
                                uu____14286
                            else
                              (let guard =
                                 let uu____14289 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14289 in
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
                          let uu____14303 =
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
                                 | FStar_Syntax_Syntax.Tm_arrow uu____14326
                                     -> (e, t_annot, guard1)
                                 | uu____14341 ->
                                     let lc =
                                       let uu____14343 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed in
                                       FStar_All.pipe_right uu____14343
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     let uu____14344 =
                                       FStar_TypeChecker_Util.check_has_type
                                         env1 e lc t1 in
                                     (match uu____14344 with
                                      | (e1, uu____14358, guard') ->
                                          let uu____14360 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard' in
                                          (e1, t_annot, uu____14360)))
                            | FStar_Pervasives_Native.None ->
                                (e, tfun_computed, guard1) in
                          (match uu____14303 with
                           | (e1, tfun, guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun in
                               let uu____14371 =
                                 let uu____14376 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____14376 guard2 in
                               (match uu____14371 with
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
              (let uu____14426 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____14426
               then
                 let uu____14427 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos in
                 let uu____14428 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14427
                   uu____14428
               else ());
              (let monadic_application uu____14507 subst arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____14507 with
                 | (head1, chead1, ghead1, cres) ->
                     let uu____14576 =
                       check_no_escape (FStar_Pervasives_Native.Some head1)
                         env fvs (FStar_Syntax_Util.comp_result cres) in
                     (match uu____14576 with
                      | (rt, g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt in
                          let uu____14590 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____14606 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____14606 in
                                (cres1, g)
                            | uu____14607 ->
                                let g =
                                  let uu____14617 =
                                    let uu____14618 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard in
                                    FStar_All.pipe_right uu____14618
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env) in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____14617 in
                                let uu____14619 =
                                  let uu____14620 =
                                    FStar_Syntax_Util.arrow bs cres1 in
                                  FStar_Syntax_Syntax.mk_Total uu____14620 in
                                (uu____14619, g) in
                          (match uu____14590 with
                           | (cres2, guard1) ->
                               ((let uu____14630 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium in
                                 if uu____14630
                                 then
                                   let uu____14631 =
                                     FStar_Syntax_Print.comp_to_string cres2 in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____14631
                                 else ());
                                (let uu____14633 =
                                   let uu____14638 =
                                     let uu____14639 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         chead1 in
                                     FStar_All.pipe_right uu____14639
                                       FStar_TypeChecker_Common.lcomp_of_comp in
                                   let uu____14640 =
                                     let uu____14641 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         cres2 in
                                     FStar_All.pipe_right uu____14641
                                       FStar_TypeChecker_Common.lcomp_of_comp in
                                   (uu____14638, uu____14640) in
                                 match uu____14633 with
                                 | (chead2, cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____14664 ->
                                                 match uu____14664 with
                                                 | (uu____14673, uu____14674,
                                                    lc) ->
                                                     (let uu____14682 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc in
                                                      Prims.op_Negation
                                                        uu____14682)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev) in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head1
                                           (FStar_List.rev arg_rets_rev)
                                           head1.FStar_Syntax_Syntax.pos in
                                       let uu____14692 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful in
                                       if uu____14692
                                       then
                                         ((let uu____14694 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____14694
                                           then
                                             let uu____14695 =
                                               FStar_Syntax_Print.term_to_string
                                                 term in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____14695
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____14699 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____14699
                                           then
                                             let uu____14700 =
                                               FStar_Syntax_Print.term_to_string
                                                 term in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____14700
                                           else ());
                                          cres3) in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c ->
                                            fun uu____14728 ->
                                              match uu____14728 with
                                              | ((e, q), x, c) ->
                                                  ((let uu____14770 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14770
                                                    then
                                                      let uu____14771 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                            -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1 in
                                                      let uu____14773 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e in
                                                      let uu____14774 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____14771
                                                        uu____14773
                                                        uu____14774
                                                    else ());
                                                   (let uu____14776 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c in
                                                    if uu____14776
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
                                       (let uu____14784 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme in
                                        if uu____14784
                                        then
                                          let uu____14785 =
                                            FStar_Syntax_Print.term_to_string
                                              head1 in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____14785
                                        else ());
                                       (let uu____14787 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2 in
                                        if uu____14787
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
                                       let uu____14794 =
                                         let uu____14795 =
                                           FStar_Syntax_Subst.compress head1 in
                                         uu____14795.FStar_Syntax_Syntax.n in
                                       match uu____14794 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____14799 -> false in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1 ->
                                                fun uu____14820 ->
                                                  match uu____14820 with
                                                  | (arg, uu____14834,
                                                     uu____14835) -> arg ::
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
                                         (let uu____14843 =
                                            let map_fun uu____14909 =
                                              match uu____14909 with
                                              | ((e, q), uu____14950, c) ->
                                                  ((let uu____14973 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14973
                                                    then
                                                      let uu____14974 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e in
                                                      let uu____14975 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____14974
                                                        uu____14975
                                                    else ());
                                                   (let uu____14977 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c in
                                                    if uu____14977
                                                    then
                                                      ((let uu____15001 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme in
                                                        if uu____15001
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
                                                           (let uu____15036 =
                                                              let uu____15037
                                                                =
                                                                let uu____15038
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head1 in
                                                                uu____15038.FStar_Syntax_Syntax.n in
                                                              match uu____15037
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____15042
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore" in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____15042
                                                              | uu____15043
                                                                  -> true in
                                                            Prims.op_Negation
                                                              uu____15036) in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____15045 =
                                                            let uu____15050 =
                                                              let uu____15051
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e in
                                                              let uu____15052
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  c.FStar_TypeChecker_Common.eff_name in
                                                              let uu____15053
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____15051
                                                                uu____15052
                                                                uu____15053 in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____15050) in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____15045)
                                                       else ();
                                                       (let uu____15056 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme in
                                                        if uu____15056
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
                                                        let uu____15060 =
                                                          let uu____15069 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          (uu____15069, q) in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____15060))))) in
                                            let uu____15098 =
                                              let uu____15129 =
                                                let uu____15158 =
                                                  let uu____15169 =
                                                    let uu____15178 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head1 in
                                                    (uu____15178,
                                                      FStar_Pervasives_Native.None,
                                                      chead2) in
                                                  uu____15169 ::
                                                    arg_comps_rev in
                                                FStar_List.map map_fun
                                                  uu____15158 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____15129 in
                                            match uu____15098 with
                                            | (lifted_args, reverse_args) ->
                                                let uu____15379 =
                                                  let uu____15380 =
                                                    FStar_List.hd
                                                      reverse_args in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15380 in
                                                let uu____15401 =
                                                  let uu____15402 =
                                                    FStar_List.tl
                                                      reverse_args in
                                                  FStar_List.rev uu____15402 in
                                                (lifted_args, uu____15379,
                                                  uu____15401) in
                                          match uu____14843 with
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
                                                uu___6_15511 =
                                                match uu___6_15511 with
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
                                                      let uu____15572 =
                                                        let uu____15573 =
                                                          let uu____15586 =
                                                            let uu____15589 =
                                                              let uu____15590
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x in
                                                              [uu____15590] in
                                                            FStar_Syntax_Subst.close
                                                              uu____15589 e in
                                                          ((false, [lb]),
                                                            uu____15586) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____15573 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____15572
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
                                     let uu____15639 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1 in
                                     (match uu____15639 with
                                      | (comp2, g) ->
                                          ((let uu____15656 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme in
                                            if uu____15656
                                            then
                                              let uu____15657 =
                                                FStar_Syntax_Print.term_to_string
                                                  app in
                                              let uu____15658 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____15657 uu____15658
                                            else ());
                                           (app, comp2, g))))))) in
               let rec tc_args head_info uu____15744 bs args1 =
                 match uu____15744 with
                 | (subst, outargs, arg_rets, g, fvs) ->
                     (match (bs, args1) with
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15907))::rest,
                         (uu____15909, FStar_Pervasives_Native.None)::uu____15910)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort in
                          let uu____15970 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head) env fvs t in
                          (match uu____15970 with
                           | (t1, g_ex) ->
                               let r1 =
                                 match outargs with
                                 | [] -> head.FStar_Syntax_Syntax.pos
                                 | ((t2, uu____16001), uu____16002,
                                    uu____16003)::uu____16004 ->
                                     let uu____16059 =
                                       FStar_Range.def_range
                                         head.FStar_Syntax_Syntax.pos in
                                     let uu____16060 =
                                       let uu____16061 =
                                         FStar_Range.use_range
                                           head.FStar_Syntax_Syntax.pos in
                                       let uu____16062 =
                                         FStar_Range.use_range
                                           t2.FStar_Syntax_Syntax.pos in
                                       FStar_Range.union_rng uu____16061
                                         uu____16062 in
                                     FStar_Range.range_of_rng uu____16059
                                       uu____16060 in
                               let uu____16063 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   r1 env t1 in
                               (match uu____16063 with
                                | (varg, uu____16083, implicits) ->
                                    let subst1 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst in
                                    let arg =
                                      let uu____16111 =
                                        FStar_Syntax_Syntax.as_implicit true in
                                      (varg, uu____16111) in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits in
                                    let uu____16119 =
                                      let uu____16162 =
                                        let uu____16181 =
                                          let uu____16198 =
                                            let uu____16199 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_All.pipe_right uu____16199
                                              FStar_TypeChecker_Common.lcomp_of_comp in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____16198) in
                                        uu____16181 :: outargs in
                                      (subst1, uu____16162, (arg ::
                                        arg_rets), guard, fvs) in
                                    tc_args head_info uu____16119 rest args1))
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau_or_attr))::rest,
                         (uu____16269, FStar_Pervasives_Native.None)::uu____16270)
                          ->
                          let uu____16329 =
                            match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let tau1 = FStar_Syntax_Subst.subst subst tau in
                                let uu____16342 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau1 in
                                (match uu____16342 with
                                 | (tau2, uu____16354, g_tau) ->
                                     let uu____16356 =
                                       let uu____16357 =
                                         let uu____16364 =
                                           FStar_Dyn.mkdyn env in
                                         (uu____16364, tau2) in
                                       FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                         uu____16357 in
                                     (uu____16356, g_tau))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let attr1 =
                                  FStar_Syntax_Subst.subst subst attr in
                                let uu____16371 =
                                  tc_tot_or_gtot_term env attr1 in
                                (match uu____16371 with
                                 | (attr2, uu____16383, g_attr) ->
                                     ((FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                         attr2), g_attr)) in
                          (match uu____16329 with
                           | (ctx_uvar_meta, g_tau_or_attr) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____16394 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head) env
                                   fvs t in
                               (match uu____16394 with
                                | (t1, g_ex) ->
                                    let r1 =
                                      match outargs with
                                      | [] -> head.FStar_Syntax_Syntax.pos
                                      | ((t2, uu____16425), uu____16426,
                                         uu____16427)::uu____16428 ->
                                          let uu____16483 =
                                            FStar_Range.def_range
                                              head.FStar_Syntax_Syntax.pos in
                                          let uu____16484 =
                                            let uu____16485 =
                                              FStar_Range.use_range
                                                head.FStar_Syntax_Syntax.pos in
                                            let uu____16486 =
                                              FStar_Range.use_range
                                                t2.FStar_Syntax_Syntax.pos in
                                            FStar_Range.union_rng uu____16485
                                              uu____16486 in
                                          FStar_Range.range_of_rng
                                            uu____16483 uu____16484 in
                                    let uu____16487 =
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        r1 env t1 FStar_Syntax_Syntax.Strict
                                        (FStar_Pervasives_Native.Some
                                           ctx_uvar_meta) in
                                    (match uu____16487 with
                                     | (varg, uu____16507, implicits) ->
                                         let subst1 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst in
                                         let arg =
                                           let uu____16535 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true in
                                           (varg, uu____16535) in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau_or_attr]
                                             implicits in
                                         let uu____16543 =
                                           let uu____16586 =
                                             let uu____16605 =
                                               let uu____16622 =
                                                 let uu____16623 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1 in
                                                 FStar_All.pipe_right
                                                   uu____16623
                                                   FStar_TypeChecker_Common.lcomp_of_comp in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16622) in
                                             uu____16605 :: outargs in
                                           (subst1, uu____16586, (arg ::
                                             arg_rets), guard, fvs) in
                                         tc_args head_info uu____16543 rest
                                           args1)))
                      | ((x, aqual)::rest, (e, aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16763, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16764)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16771),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16772)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16777),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16778)) ->
                                ()
                            | (FStar_Pervasives_Native.None,
                               FStar_Pervasives_Native.None) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality),
                               FStar_Pervasives_Native.None) -> ()
                            | uu____16791 ->
                                let uu____16800 =
                                  let uu____16805 =
                                    let uu____16806 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual in
                                    let uu____16807 =
                                      FStar_Syntax_Print.aqual_to_string aq in
                                    let uu____16808 =
                                      FStar_Syntax_Print.bv_to_string x in
                                    let uu____16809 =
                                      FStar_Syntax_Print.term_to_string e in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____16806 uu____16807 uu____16808
                                      uu____16809 in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____16805) in
                                FStar_Errors.raise_error uu____16800
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst aqual in
                            let x1 =
                              let uu___2372_16813 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2372_16813.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2372_16813.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____16815 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____16815
                             then
                               let uu____16816 =
                                 FStar_Syntax_Print.bv_to_string x1 in
                               let uu____16817 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort in
                               let uu____16818 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____16819 =
                                 FStar_Syntax_Print.subst_to_string subst in
                               let uu____16820 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____16816 uu____16817 uu____16818
                                 uu____16819 uu____16820
                             else ());
                            (let uu____16822 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head) env fvs
                                 targ in
                             match uu____16822 with
                             | (targ1, g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1 in
                                 let env2 =
                                   let uu___2381_16837 = env1 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2381_16837.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2381_16837.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2381_16837.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2381_16837.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2381_16837.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2381_16837.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2381_16837.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2381_16837.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2381_16837.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2381_16837.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2381_16837.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2381_16837.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2381_16837.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2381_16837.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2381_16837.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2381_16837.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___2381_16837.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2381_16837.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2381_16837.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2381_16837.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2381_16837.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2381_16837.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2381_16837.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2381_16837.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2381_16837.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2381_16837.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2381_16837.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2381_16837.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2381_16837.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2381_16837.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2381_16837.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2381_16837.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2381_16837.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2381_16837.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2381_16837.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2381_16837.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2381_16837.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2381_16837.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2381_16837.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2381_16837.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2381_16837.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2381_16837.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2381_16837.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2381_16837.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2381_16837.FStar_TypeChecker_Env.erasable_types_tab);
                                     FStar_TypeChecker_Env.enable_defer_to_tac
                                       =
                                       (uu___2381_16837.FStar_TypeChecker_Env.enable_defer_to_tac)
                                   } in
                                 ((let uu____16839 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High in
                                   if uu____16839
                                   then
                                     let uu____16840 =
                                       FStar_Syntax_Print.tag_of_term e in
                                     let uu____16841 =
                                       FStar_Syntax_Print.term_to_string e in
                                     let uu____16842 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1 in
                                     let uu____16843 =
                                       FStar_Util.string_of_bool
                                         env2.FStar_TypeChecker_Env.use_eq in
                                     FStar_Util.print4
                                       "Checking arg (%s) %s at type %s with use_eq:%s\n"
                                       uu____16840 uu____16841 uu____16842
                                       uu____16843
                                   else ());
                                  (let uu____16845 = tc_term env2 e in
                                   match uu____16845 with
                                   | (e1, c, g_e) ->
                                       let g1 =
                                         let uu____16862 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____16862 in
                                       let arg = (e1, aq) in
                                       let xterm =
                                         let uu____16885 =
                                           let uu____16888 =
                                             let uu____16897 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16897 in
                                           FStar_Pervasives_Native.fst
                                             uu____16888 in
                                         (uu____16885, aq) in
                                       let uu____16906 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name) in
                                       if uu____16906
                                       then
                                         let subst1 =
                                           let uu____16914 = FStar_List.hd bs in
                                           maybe_extend_subst subst
                                             uu____16914 e1 in
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
                      | (uu____17060, []) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([], arg::uu____17096) ->
                          let uu____17147 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs [] in
                          (match uu____17147 with
                           | (head1, chead1, ghead1) ->
                               let uu____17169 =
                                 let uu____17174 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1 in
                                 FStar_All.pipe_right uu____17174
                                   (fun uu____17191 ->
                                      match uu____17191 with
                                      | (c, g1) ->
                                          let uu____17202 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1 in
                                          (c, uu____17202)) in
                               (match uu____17169 with
                                | (chead2, ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____17241 =
                                          FStar_Syntax_Subst.compress tres in
                                        FStar_All.pipe_right uu____17241
                                          FStar_Syntax_Util.unrefine in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1, cres') ->
                                          let uu____17272 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres' in
                                          (match uu____17272 with
                                           | (bs2, cres'1) ->
                                               let head_info1 =
                                                 (head1, chead2, ghead3,
                                                   cres'1) in
                                               ((let uu____17295 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low in
                                                 if uu____17295
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
                                      | uu____17353 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____17361 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env) in
                                              FStar_All.pipe_right
                                                uu____17361
                                                FStar_Syntax_Util.unascribe in
                                            let uu____17362 =
                                              let uu____17363 =
                                                FStar_Syntax_Subst.compress
                                                  tres3 in
                                              uu____17363.FStar_Syntax_Syntax.n in
                                            match uu____17362 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____17366;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____17367;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},
                                                 uu____17369)
                                                -> norm_tres tres4
                                            | uu____17376 -> tres3 in
                                          let uu____17377 = norm_tres tres1 in
                                          aux true solve ghead3 uu____17377
                                      | uu____17378 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3 in
                                          aux norm1 true ghead4 tres1
                                      | uu____17380 ->
                                          let uu____17381 =
                                            let uu____17386 =
                                              let uu____17387 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead in
                                              let uu____17388 =
                                                FStar_Util.string_of_int
                                                  n_args in
                                              let uu____17389 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____17387 uu____17388
                                                uu____17389 in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____17386) in
                                          let uu____17390 =
                                            FStar_Syntax_Syntax.argpos arg in
                                          FStar_Errors.raise_error
                                            uu____17381 uu____17390 in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2)))) in
               let rec check_function_app tf guard =
                 let uu____17418 =
                   let uu____17419 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____17419.FStar_Syntax_Syntax.n in
                 match uu____17418 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____17428 ->
                     let uu____17441 =
                       FStar_List.fold_right
                         (fun uu____17472 ->
                            fun uu____17473 ->
                              match uu____17473 with
                              | (bs, guard1) ->
                                  let uu____17500 =
                                    let uu____17513 =
                                      let uu____17514 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____17514
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17513 in
                                  (match uu____17500 with
                                   | (t, uu____17530, g) ->
                                       let uu____17544 =
                                         let uu____17547 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____17547 :: bs in
                                       let uu____17548 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____17544, uu____17548))) args
                         ([], guard) in
                     (match uu____17441 with
                      | (bs, guard1) ->
                          let uu____17565 =
                            let uu____17572 =
                              let uu____17585 =
                                let uu____17586 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____17586
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17585 in
                            match uu____17572 with
                            | (t, uu____17602, g) ->
                                let uu____17616 = FStar_Options.ml_ish () in
                                if uu____17616
                                then
                                  let uu____17623 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____17626 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____17623, uu____17626)
                                else
                                  (let uu____17630 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____17633 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____17630, uu____17633)) in
                          (match uu____17565 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____17652 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____17652
                                 then
                                   let uu____17653 =
                                     FStar_Syntax_Print.term_to_string head in
                                   let uu____17654 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____17655 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17653 uu____17654 uu____17655
                                 else ());
                                (let g =
                                   let uu____17658 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17658 in
                                 let uu____17659 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____17659))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17660;
                        FStar_Syntax_Syntax.pos = uu____17661;
                        FStar_Syntax_Syntax.vars = uu____17662;_},
                      uu____17663)
                     ->
                     let uu____17700 =
                       FStar_List.fold_right
                         (fun uu____17731 ->
                            fun uu____17732 ->
                              match uu____17732 with
                              | (bs, guard1) ->
                                  let uu____17759 =
                                    let uu____17772 =
                                      let uu____17773 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____17773
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17772 in
                                  (match uu____17759 with
                                   | (t, uu____17789, g) ->
                                       let uu____17803 =
                                         let uu____17806 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____17806 :: bs in
                                       let uu____17807 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____17803, uu____17807))) args
                         ([], guard) in
                     (match uu____17700 with
                      | (bs, guard1) ->
                          let uu____17824 =
                            let uu____17831 =
                              let uu____17844 =
                                let uu____17845 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____17845
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17844 in
                            match uu____17831 with
                            | (t, uu____17861, g) ->
                                let uu____17875 = FStar_Options.ml_ish () in
                                if uu____17875
                                then
                                  let uu____17882 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____17885 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____17882, uu____17885)
                                else
                                  (let uu____17889 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____17892 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____17889, uu____17892)) in
                          (match uu____17824 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____17911 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____17911
                                 then
                                   let uu____17912 =
                                     FStar_Syntax_Print.term_to_string head in
                                   let uu____17913 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____17914 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17912 uu____17913 uu____17914
                                 else ());
                                (let g =
                                   let uu____17917 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17917 in
                                 let uu____17918 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____17918))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                     let uu____17941 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____17941 with
                      | (bs1, c1) ->
                          let head_info = (head, chead, ghead, c1) in
                          ((let uu____17964 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme in
                            if uu____17964
                            then
                              let uu____17965 =
                                FStar_Syntax_Print.term_to_string head in
                              let uu____17966 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____17967 =
                                FStar_Syntax_Print.binders_to_string ", " bs1 in
                              let uu____17968 =
                                FStar_Syntax_Print.comp_to_string c1 in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17965 uu____17966 uu____17967
                                uu____17968
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv, uu____18027) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t, uu____18033, uu____18034) ->
                     check_function_app t guard
                 | uu____18075 ->
                     let uu____18076 =
                       FStar_TypeChecker_Err.expected_function_typ env tf in
                     FStar_Errors.raise_error uu____18076
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
                  let uu____18158 =
                    FStar_List.fold_left2
                      (fun uu____18225 ->
                         fun uu____18226 ->
                           fun uu____18227 ->
                             match (uu____18225, uu____18226, uu____18227)
                             with
                             | ((seen, guard, ghost), (e, aq), (b, aq')) ->
                                 ((let uu____18374 =
                                     let uu____18375 =
                                       FStar_Syntax_Util.eq_aqual aq aq' in
                                     uu____18375 <> FStar_Syntax_Util.Equal in
                                   if uu____18374
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____18377 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                       "arguments to short circuiting operators must be pure or ghost" in
                                   match uu____18377 with
                                   | (e1, c1, g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen in
                                       let g1 =
                                         let uu____18405 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____18405 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____18409 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____18409)
                                              &&
                                              (let uu____18411 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name in
                                               Prims.op_Negation uu____18411)) in
                                       let uu____18412 =
                                         let uu____18423 =
                                           let uu____18434 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____18434] in
                                         FStar_List.append seen uu____18423 in
                                       let uu____18467 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1 in
                                       (uu____18412, uu____18467, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____18158 with
                   | (args1, guard, ghost) ->
                       let e = FStar_Syntax_Syntax.mk_Tm_app head args1 r in
                       let c1 =
                         if ghost
                         then
                           let uu____18527 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____18527
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c in
                       let uu____18529 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____18529 with | (c2, g) -> (e, c2, g)))
              | uu____18545 ->
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
            let uu____18637 = FStar_Syntax_Util.head_and_args t1 in
            match uu____18637 with
            | (head, args) ->
                let uu____18680 =
                  let uu____18681 = FStar_Syntax_Subst.compress head in
                  uu____18681.FStar_Syntax_Syntax.n in
                (match uu____18680 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18685;
                        FStar_Syntax_Syntax.vars = uu____18686;_},
                      us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18693 ->
                     if norm1
                     then t1
                     else
                       (let uu____18695 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1 in
                        aux true uu____18695))
          and unfold_once t f us args =
            let uu____18712 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            if uu____18712
            then t
            else
              (let uu____18714 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               match uu____18714 with
               | FStar_Pervasives_Native.None -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____18734 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
                   (match uu____18734 with
                    | (uu____18739, head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            t.FStar_Syntax_Syntax.pos in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t' in
                        aux false t'1)) in
          let uu____18743 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t in
          aux false uu____18743 in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____18761 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____18761
           then
             let uu____18762 = FStar_Syntax_Print.term_to_string pat_t1 in
             let uu____18763 = FStar_Syntax_Print.term_to_string scrutinee_t in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____18762 uu____18763
           else ());
          (let fail1 msg =
             let msg1 =
               let uu____18777 = FStar_Syntax_Print.term_to_string pat_t1 in
               let uu____18778 =
                 FStar_Syntax_Print.term_to_string scrutinee_t in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____18777 uu____18778 msg in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p in
           let uu____18779 = FStar_Syntax_Util.head_and_args scrutinee_t in
           match uu____18779 with
           | (head_s, args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1 in
               let uu____18823 = FStar_Syntax_Util.un_uinst head_s in
               (match uu____18823 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____18824;
                    FStar_Syntax_Syntax.pos = uu____18825;
                    FStar_Syntax_Syntax.vars = uu____18826;_} ->
                    let uu____18829 = FStar_Syntax_Util.head_and_args pat_t2 in
                    (match uu____18829 with
                     | (head_p, args_p) ->
                         let uu____18872 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s in
                         if uu____18872
                         then
                           let uu____18873 =
                             let uu____18874 =
                               FStar_Syntax_Util.un_uinst head_p in
                             uu____18874.FStar_Syntax_Syntax.n in
                           (match uu____18873 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____18879 =
                                    let uu____18880 =
                                      let uu____18881 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____18881 in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____18880 in
                                  if uu____18879
                                  then
                                    fail1
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail1 ""
                                 else ();
                                 (let uu____18901 =
                                    let uu____18926 =
                                      let uu____18929 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18929 in
                                    match uu____18926 with
                                    | FStar_Pervasives_Native.None ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n ->
                                        let uu____18975 =
                                          FStar_Util.first_N n args_p in
                                        (match uu____18975 with
                                         | (params_p, uu____19033) ->
                                             let uu____19074 =
                                               FStar_Util.first_N n args_s in
                                             (match uu____19074 with
                                              | (params_s, uu____19132) ->
                                                  (params_p, params_s))) in
                                  match uu____18901 with
                                  | (params_p, params_s) ->
                                      FStar_List.fold_left2
                                        (fun out ->
                                           fun uu____19261 ->
                                             fun uu____19262 ->
                                               match (uu____19261,
                                                       uu____19262)
                                               with
                                               | ((p, uu____19296),
                                                  (s, uu____19298)) ->
                                                   let uu____19331 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s in
                                                   (match uu____19331 with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        let uu____19334 =
                                                          let uu____19335 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p in
                                                          let uu____19336 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____19335
                                                            uu____19336 in
                                                        fail1 uu____19334
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____19339 ->
                                fail1 "Pattern matching a non-inductive type")
                         else
                           (let uu____19341 =
                              let uu____19342 =
                                FStar_Syntax_Print.term_to_string head_p in
                              let uu____19343 =
                                FStar_Syntax_Print.term_to_string head_s in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____19342 uu____19343 in
                            fail1 uu____19341))
                | uu____19344 ->
                    let uu____19345 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t in
                    (match uu____19345 with
                     | FStar_Pervasives_Native.None -> fail1 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g in
                         g1))) in
        let type_of_simple_pat env1 e =
          let uu____19385 = FStar_Syntax_Util.head_and_args e in
          match uu____19385 with
          | (head, args) ->
              (match head.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____19453 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____19453 with
                    | (us, t_f) ->
                        let uu____19472 = FStar_Syntax_Util.arrow_formals t_f in
                        (match uu____19472 with
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
                              (let rec aux uu____19577 formals1 args1 =
                                 match uu____19577 with
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
                                          let uu____19720 =
                                            FStar_Syntax_Subst.subst subst t in
                                          (pat_e, uu____19720, bvs, guard,
                                            erasable)
                                      | ((f1, uu____19724)::formals2,
                                         (a, imp_a)::args2) ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst
                                              f1.FStar_Syntax_Syntax.sort in
                                          let uu____19782 =
                                            let uu____19803 =
                                              let uu____19804 =
                                                FStar_Syntax_Subst.compress a in
                                              uu____19804.FStar_Syntax_Syntax.n in
                                            match uu____19803 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2688_19829 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2688_19829.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2688_19829.FStar_Syntax_Syntax.index);
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
                                                uu____19852 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1 in
                                                let uu____19866 =
                                                  tc_tot_or_gtot_term env2 a in
                                                (match uu____19866 with
                                                 | (a1, uu____19894, g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g in
                                                     let subst1 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst in
                                                     ((a1, imp_a), subst1,
                                                       bvs, g1))
                                            | uu____19918 ->
                                                fail "Not a simple pattern" in
                                          (match uu____19782 with
                                           | (a1, subst1, bvs1, g) ->
                                               let uu____19979 =
                                                 let uu____20002 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard in
                                                 (subst1,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____20002) in
                                               aux uu____19979 formals2 args2)
                                      | uu____20041 ->
                                          fail "Not a fully applued pattern") in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____20096 -> fail "Not a simple pattern") in
        let rec check_nested_pattern env1 p t =
          (let uu____20158 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____20158
           then
             let uu____20159 = FStar_Syntax_Print.pat_to_string p in
             let uu____20160 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____20159
               uu____20160
           else ());
          (let id =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____20181 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t in
               FStar_All.pipe_right uu____20181 FStar_Syntax_Syntax.mk_binder in
             let tm =
               let uu____20189 =
                 let uu____20190 =
                   let uu____20199 =
                     let uu____20200 =
                       FStar_All.pipe_right x_b FStar_Pervasives_Native.fst in
                     FStar_All.pipe_right uu____20200
                       FStar_Syntax_Syntax.bv_to_name in
                   FStar_All.pipe_right uu____20199
                     FStar_Syntax_Syntax.as_arg in
                 [uu____20190] in
               FStar_Syntax_Syntax.mk_Tm_app disc uu____20189
                 FStar_Range.dummyRange in
             let tm1 =
               let uu____20234 =
                 let uu____20235 =
                   FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg in
                 [uu____20235] in
               FStar_Syntax_Syntax.mk_Tm_app inner_t uu____20234
                 FStar_Range.dummyRange in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____20296 ->
               let uu____20303 =
                 let uu____20304 = FStar_Syntax_Print.pat_to_string p in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____20304 in
               failwith uu____20303
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2727_20323 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2727_20323.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2727_20323.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____20324 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], [id], uu____20324,
                 (let uu___2730_20330 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2730_20330.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2734_20333 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2734_20333.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2734_20333.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____20334 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], [id], uu____20334,
                 (let uu___2737_20340 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2737_20340.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant c ->
               ((match c with
                 | FStar_Const.Const_unit -> ()
                 | FStar_Const.Const_bool uu____20343 -> ()
                 | FStar_Const.Const_int uu____20344 -> ()
                 | FStar_Const.Const_char uu____20355 -> ()
                 | FStar_Const.Const_float uu____20356 -> ()
                 | FStar_Const.Const_string uu____20357 -> ()
                 | uu____20362 ->
                     let uu____20363 =
                       let uu____20364 = FStar_Syntax_Print.const_to_string c in
                       FStar_Util.format1
                         "Pattern matching a constant that does not have decidable equality: %s"
                         uu____20364 in
                     fail uu____20363);
                (let uu____20365 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p in
                 match uu____20365 with
                 | (uu____20392, e_c, uu____20394, uu____20395) ->
                     let uu____20400 = tc_tot_or_gtot_term env1 e_c in
                     (match uu____20400 with
                      | (e_c1, lc, g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                           (let expected_t =
                              expected_pat_typ env1 p0.FStar_Syntax_Syntax.p
                                t in
                            (let uu____20429 =
                               let uu____20430 =
                                 FStar_TypeChecker_Rel.teq_nosmt_force env1
                                   lc.FStar_TypeChecker_Common.res_typ
                                   expected_t in
                               Prims.op_Negation uu____20430 in
                             if uu____20429
                             then
                               let uu____20431 =
                                 let uu____20432 =
                                   FStar_Syntax_Print.term_to_string
                                     lc.FStar_TypeChecker_Common.res_typ in
                                 let uu____20433 =
                                   FStar_Syntax_Print.term_to_string
                                     expected_t in
                                 FStar_Util.format2
                                   "Type of pattern (%s) does not match type of scrutinee (%s)"
                                   uu____20432 uu____20433 in
                               fail uu____20431
                             else ());
                            ([], [], e_c1, p,
                              FStar_TypeChecker_Env.trivial_guard, false))))))
           | FStar_Syntax_Syntax.Pat_cons (fv, sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20485 ->
                        match uu____20485 with
                        | (p1, b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____20510
                                 -> (p1, b)
                             | uu____20519 ->
                                 let uu____20520 =
                                   let uu____20523 =
                                     let uu____20524 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun in
                                     FStar_Syntax_Syntax.Pat_var uu____20524 in
                                   FStar_Syntax_Syntax.withinfo uu____20523
                                     p1.FStar_Syntax_Syntax.p in
                                 (uu____20520, b))) sub_pats in
                 let uu___2778_20527 = p in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2778_20527.FStar_Syntax_Syntax.p)
                 } in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____20567 ->
                         match uu____20567 with
                         | (x, uu____20575) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____20580
                                  -> false
                              | uu____20587 -> true))) in
               let uu____20588 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat in
               (match uu____20588 with
                | (simple_bvs, simple_pat_e, g0, simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____20628 =
                          let uu____20629 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p in
                          let uu____20630 =
                            FStar_Syntax_Print.pat_to_string simple_pat in
                          let uu____20631 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1) in
                          let uu____20636 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs) in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____20629 uu____20630 uu____20631 uu____20636 in
                        failwith uu____20628)
                     else ();
                     (let uu____20638 =
                        let uu____20649 =
                          type_of_simple_pat env1 simple_pat_e in
                        match uu____20649 with
                        | (simple_pat_e1, simple_pat_t, simple_bvs1, guard,
                           erasable) ->
                            let g' =
                              let uu____20682 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t in
                              pat_typ_ok env1 simple_pat_t uu____20682 in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g' in
                            ((let uu____20685 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns") in
                              if uu____20685
                              then
                                let uu____20686 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1 in
                                let uu____20687 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t in
                                let uu____20688 =
                                  let uu____20689 =
                                    FStar_List.map
                                      (fun x ->
                                         let uu____20695 =
                                           let uu____20696 =
                                             FStar_Syntax_Print.bv_to_string
                                               x in
                                           let uu____20697 =
                                             let uu____20698 =
                                               let uu____20699 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort in
                                               Prims.op_Hat uu____20699 ")" in
                                             Prims.op_Hat " : " uu____20698 in
                                           Prims.op_Hat uu____20696
                                             uu____20697 in
                                         Prims.op_Hat "(" uu____20695)
                                      simple_bvs1 in
                                  FStar_All.pipe_right uu____20689
                                    (FStar_String.concat " ") in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____20686 uu____20687 uu____20688
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable)) in
                      match uu____20638 with
                      | (simple_pat_e1, simple_bvs1, g1, erasable) ->
                          let uu____20729 =
                            let uu____20758 =
                              let uu____20787 =
                                FStar_TypeChecker_Env.conj_guard g0 g1 in
                              (env1, [], [], [], [], uu____20787, erasable,
                                Prims.int_zero) in
                            FStar_List.fold_left2
                              (fun uu____20860 ->
                                 fun uu____20861 ->
                                   fun x ->
                                     match (uu____20860, uu____20861) with
                                     | ((env2, bvs, tms, pats, subst, g,
                                         erasable1, i),
                                        (p1, b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst
                                             x.FStar_Syntax_Syntax.sort in
                                         let uu____21022 =
                                           check_nested_pattern env2 p1
                                             expected_t in
                                         (match uu____21022 with
                                          | (bvs_p, tms_p, e_p, p2, g',
                                             erasable_p) ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____21086 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____21086 i in
                                                let uu____21087 =
                                                  let uu____21096 =
                                                    let uu____21101 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None in
                                                    mk_disc_t uu____21101 in
                                                  FStar_List.map uu____21096 in
                                                FStar_All.pipe_right tms_p
                                                  uu____21087 in
                                              let uu____21106 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g' in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append tms tms_p1),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst),
                                                uu____21106,
                                                (erasable1 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____20758 sub_pats1 simple_bvs1 in
                          (match uu____20729 with
                           | (_env, bvs, tms, checked_sub_pats, subst, g,
                              erasable1, uu____21156) ->
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
                                              let uu___2862_21313 = hd in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2862_21313.FStar_Syntax_Syntax.p)
                                              } in
                                            let uu____21318 =
                                              aux simple_pats1 bvs1 sub_pats2 in
                                            (hd1, b) :: uu____21318
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,
                                                (hd1, uu____21357)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____21389 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3 in
                                                 (hd1, b) :: uu____21389
                                             | uu____21406 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____21429 ->
                                            failwith
                                              "Impossible: expected a simple pattern") in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1, simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats in
                                     let uu___2883_21467 = pat in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2883_21467.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____21478 -> failwith "Impossible" in
                               let uu____21481 =
                                 reconstruct_nested_pat simple_pat_elab in
                               (bvs, tms, pat_e, uu____21481, g, erasable1)))))) in
        (let uu____21487 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns") in
         if uu____21487
         then
           let uu____21488 = FStar_Syntax_Print.pat_to_string p0 in
           FStar_Util.print1 "Checking pattern: %s\n" uu____21488
         else ());
        (let uu____21490 =
           let uu____21507 =
             let uu___2888_21508 =
               let uu____21509 = FStar_TypeChecker_Env.clear_expected_typ env in
               FStar_All.pipe_right uu____21509 FStar_Pervasives_Native.fst in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2888_21508.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2888_21508.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2888_21508.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2888_21508.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2888_21508.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2888_21508.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2888_21508.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2888_21508.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2888_21508.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2888_21508.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2888_21508.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2888_21508.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2888_21508.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2888_21508.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2888_21508.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2888_21508.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___2888_21508.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2888_21508.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2888_21508.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2888_21508.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2888_21508.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2888_21508.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2888_21508.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2888_21508.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2888_21508.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2888_21508.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2888_21508.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2888_21508.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2888_21508.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2888_21508.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2888_21508.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2888_21508.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2888_21508.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2888_21508.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2888_21508.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2888_21508.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2888_21508.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2888_21508.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2888_21508.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2888_21508.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2888_21508.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2888_21508.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2888_21508.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2888_21508.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2888_21508.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___2888_21508.FStar_TypeChecker_Env.enable_defer_to_tac)
             } in
           let uu____21524 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0 in
           check_nested_pattern uu____21507 uu____21524 pat_t in
         match uu____21490 with
         | (bvs, tms, pat_e, pat, g, erasable) ->
             ((let uu____21560 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns") in
               if uu____21560
               then
                 let uu____21561 = FStar_Syntax_Print.pat_to_string pat in
                 let uu____21562 = FStar_Syntax_Print.term_to_string pat_e in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____21561
                   uu____21562
               else ());
              (let uu____21564 = FStar_TypeChecker_Env.push_bvs env bvs in
               let uu____21565 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e in
               (pat, bvs, tms, uu____21564, pat_e, uu____21565, g, erasable))))
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
        let uu____21600 = FStar_Syntax_Subst.open_branch branch in
        match uu____21600 with
        | (pattern, when_clause, branch_exp) ->
            let uu____21647 = branch in
            (match uu____21647 with
             | (cpat, uu____21676, cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____21698 =
                   let uu____21705 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____21705
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____21698 with
                  | (scrutinee_env, uu____21740) ->
                      let uu____21745 = tc_pat env pat_t pattern in
                      (match uu____21745 with
                       | (pattern1, pat_bvs, pat_bv_tms, pat_env, pat_exp,
                          norm_pat_exp, guard_pat, erasable) ->
                           ((let uu____21810 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme in
                             if uu____21810
                             then
                               let uu____21811 =
                                 FStar_Syntax_Print.pat_to_string pattern1 in
                               let uu____21812 =
                                 FStar_Syntax_Print.bvs_to_string ";" pat_bvs in
                               let uu____21813 =
                                 FStar_List.fold_left
                                   (fun s ->
                                      fun t ->
                                        let uu____21819 =
                                          let uu____21820 =
                                            FStar_Syntax_Print.term_to_string
                                              t in
                                          Prims.op_Hat ";" uu____21820 in
                                        Prims.op_Hat s uu____21819) ""
                                   pat_bv_tms in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____21811 uu____21812 uu____21813
                             else ());
                            (let uu____21822 =
                               match when_clause with
                               | FStar_Pervasives_Native.None ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____21852 =
                                     FStar_TypeChecker_Env.should_verify env in
                                   if uu____21852
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____21870 =
                                        let uu____21877 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool in
                                        tc_term uu____21877 e in
                                      match uu____21870 with
                                      | (e1, c, g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g)) in
                             match uu____21822 with
                             | (when_clause1, g_when) ->
                                 let uu____21932 = tc_term pat_env branch_exp in
                                 (match uu____21932 with
                                  | (branch_exp1, c, g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____21988 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool in
                                              FStar_All.pipe_left
                                                (fun uu____21999 ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____21999) uu____21988 in
                                        let branch_guard =
                                          let uu____22003 =
                                            let uu____22004 =
                                              FStar_TypeChecker_Env.should_verify
                                                env in
                                            Prims.op_Negation uu____22004 in
                                          if uu____22003
                                          then
                                            FStar_Syntax_Util.exp_true_bool
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____22057 =
                                                   let uu____22064 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____22064 in
                                                 match uu____22057 with
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
                                                       let uu____22076 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator in
                                                       (match uu____22076
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                            -> []
                                                        | uu____22097 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None in
                                                            let uu____22109 =
                                                              let uu____22110
                                                                =
                                                                let uu____22111
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2 in
                                                                [uu____22111] in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____22110
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                            [uu____22109])
                                                     else [] in
                                               let fail uu____22142 =
                                                 let uu____22143 =
                                                   let uu____22144 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos in
                                                   let uu____22145 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1 in
                                                   let uu____22146 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1 in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____22144 uu____22145
                                                     uu____22146 in
                                                 failwith uu____22143 in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1, uu____22159) ->
                                                     head_constructor t1
                                                 | uu____22164 -> fail () in
                                               let force_scrutinee
                                                 uu____22170 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     let uu____22171 =
                                                       let uu____22172 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p in
                                                       let uu____22173 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2 in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____22172
                                                         uu____22173 in
                                                     failwith uu____22171
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t in
                                               let pat_exp2 =
                                                 let uu____22178 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1 in
                                                 FStar_All.pipe_right
                                                   uu____22178
                                                   FStar_Syntax_Util.unmeta in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____22183,
                                                  FStar_Syntax_Syntax.Tm_name
                                                  uu____22184) -> []
                                               | (uu____22185,
                                                  FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,
                                                  FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____22188 =
                                                     let uu____22189 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1 in
                                                     let uu____22190 =
                                                       force_scrutinee () in
                                                     FStar_Syntax_Util.mk_decidable_eq
                                                       uu____22189
                                                       uu____22190 pat_exp2 in
                                                   [uu____22188]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____22193,
                                                   FStar_Pervasives_Native.Some
                                                   uu____22194)),
                                                  uu____22195) ->
                                                   let uu____22210 =
                                                     let uu____22217 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env in
                                                     match uu____22217 with
                                                     | (env1, uu____22231) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2 in
                                                   (match uu____22210 with
                                                    | (uu____22238, t,
                                                       uu____22240) ->
                                                        let uu____22241 =
                                                          let uu____22242 =
                                                            force_scrutinee
                                                              () in
                                                          FStar_Syntax_Util.mk_decidable_eq
                                                            t uu____22242
                                                            pat_exp2 in
                                                        [uu____22241])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22245, []),
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                  uu____22246) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2 in
                                                   let uu____22268 =
                                                     let uu____22269 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v in
                                                     Prims.op_Negation
                                                       uu____22269 in
                                                   if uu____22268
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22275 =
                                                        force_scrutinee () in
                                                      let uu____22278 =
                                                        head_constructor
                                                          pat_exp2 in
                                                      discriminate
                                                        uu____22275
                                                        uu____22278)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22281, []),
                                                  FStar_Syntax_Syntax.Tm_fvar
                                                  uu____22282) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2 in
                                                   let uu____22298 =
                                                     let uu____22299 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v in
                                                     Prims.op_Negation
                                                       uu____22299 in
                                                   if uu____22298
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22305 =
                                                        force_scrutinee () in
                                                      let uu____22308 =
                                                        head_constructor
                                                          pat_exp2 in
                                                      discriminate
                                                        uu____22305
                                                        uu____22308)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22311, pat_args),
                                                  FStar_Syntax_Syntax.Tm_app
                                                  (head, args)) ->
                                                   let f =
                                                     head_constructor head in
                                                   let uu____22356 =
                                                     (let uu____22359 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v in
                                                      Prims.op_Negation
                                                        uu____22359)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args)) in
                                                   if uu____22356
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____22382 =
                                                          let uu____22387 =
                                                            FStar_List.zip
                                                              pat_args args in
                                                          FStar_All.pipe_right
                                                            uu____22387
                                                            (FStar_List.mapi
                                                               (fun i ->
                                                                  fun
                                                                    uu____22469
                                                                    ->
                                                                    match uu____22469
                                                                    with
                                                                    | 
                                                                    ((pi,
                                                                    uu____22489),
                                                                    (ei,
                                                                    uu____22491))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____22516
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    match uu____22516
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____22537
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____22549
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____22549
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____22550
                                                                    =
                                                                    let uu____22551
                                                                    =
                                                                    let uu____22552
                                                                    =
                                                                    let uu____22561
                                                                    =
                                                                    force_scrutinee
                                                                    () in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____22561 in
                                                                    [uu____22552] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____22551
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____22550 in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei)) in
                                                        FStar_All.pipe_right
                                                          uu____22382
                                                          FStar_List.flatten in
                                                      let uu____22584 =
                                                        let uu____22587 =
                                                          force_scrutinee () in
                                                        discriminate
                                                          uu____22587 f in
                                                      FStar_List.append
                                                        uu____22584
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____22590, uu____22591)
                                                   -> []
                                               | uu____22598 ->
                                                   let uu____22603 =
                                                     let uu____22604 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2 in
                                                     let uu____22605 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2 in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____22604
                                                       uu____22605 in
                                                   failwith uu____22603 in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____22632 =
                                                 let uu____22633 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____22633 in
                                               if uu____22632
                                               then
                                                 FStar_Syntax_Util.exp_true_bool
                                               else
                                                 (let t =
                                                    let uu____22636 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_and_l
                                                      uu____22636 in
                                                  let uu____22645 =
                                                    tc_check_tot_or_gtot_term
                                                      scrutinee_env t
                                                      FStar_Syntax_Util.t_bool
                                                      "" in
                                                  match uu____22645 with
                                                  | (t1, uu____22653,
                                                     uu____22654) -> t1) in
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
                                        (let uu____22669 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             FStar_Options.Extreme in
                                         if uu____22669
                                         then
                                           let uu____22670 =
                                             FStar_Syntax_Print.term_to_string
                                               branch_guard in
                                           FStar_Util.print1
                                             "tc_eqn: branch guard : %s\n"
                                             uu____22670
                                         else ());
                                        (let uu____22672 =
                                           let eqs =
                                             let uu____22691 =
                                               let uu____22692 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env in
                                               Prims.op_Negation uu____22692 in
                                             if uu____22691
                                             then
                                               FStar_Pervasives_Native.None
                                             else
                                               (let e =
                                                  FStar_Syntax_Subst.compress
                                                    pat_exp in
                                                let uu____22697 =
                                                  let uu____22698 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____22698 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____22697) in
                                           let uu____22699 =
                                             FStar_TypeChecker_Util.strengthen_precondition
                                               FStar_Pervasives_Native.None
                                               env branch_exp1 c g_branch in
                                           match uu____22699 with
                                           | (c1, g_branch1) ->
                                               let branch_has_layered_effect
                                                 =
                                                 let uu____22725 =
                                                   FStar_All.pipe_right
                                                     c1.FStar_TypeChecker_Common.eff_name
                                                     (FStar_TypeChecker_Env.norm_eff_name
                                                        env) in
                                                 FStar_All.pipe_right
                                                   uu____22725
                                                   (FStar_TypeChecker_Env.is_layered_effect
                                                      env) in
                                               let uu____22726 =
                                                 let env1 =
                                                   let uu____22732 =
                                                     FStar_All.pipe_right
                                                       pat_bvs
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder) in
                                                   FStar_TypeChecker_Env.push_binders
                                                     scrutinee_env
                                                     uu____22732 in
                                                 if branch_has_layered_effect
                                                 then
                                                   let c2 =
                                                     let uu____22740 =
                                                       let uu____22741 =
                                                         FStar_Syntax_Util.b2t
                                                           branch_guard in
                                                       FStar_TypeChecker_Common.NonTrivial
                                                         uu____22741 in
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env1 c1 uu____22740 in
                                                   (c2,
                                                     FStar_TypeChecker_Env.trivial_guard)
                                                 else
                                                   (match (eqs,
                                                            when_condition)
                                                    with
                                                    | uu____22753 when
                                                        let uu____22764 =
                                                          FStar_TypeChecker_Env.should_verify
                                                            env1 in
                                                        Prims.op_Negation
                                                          uu____22764
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
                                                        let uu____22784 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 gf in
                                                        let uu____22785 =
                                                          FStar_TypeChecker_Env.imp_guard
                                                            g g_when in
                                                        (uu____22784,
                                                          uu____22785)
                                                    | (FStar_Pervasives_Native.Some
                                                       f,
                                                       FStar_Pervasives_Native.Some
                                                       w) ->
                                                        let g_f =
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            f in
                                                        let g_fw =
                                                          let uu____22800 =
                                                            FStar_Syntax_Util.mk_conj
                                                              f w in
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            uu____22800 in
                                                        let uu____22801 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 g_fw in
                                                        let uu____22802 =
                                                          let uu____22803 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              g_f in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____22803
                                                            g_when in
                                                        (uu____22801,
                                                          uu____22802)
                                                    | (FStar_Pervasives_Native.None,
                                                       FStar_Pervasives_Native.Some
                                                       w) ->
                                                        let g_w =
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            w in
                                                        let g =
                                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                                            g_w in
                                                        let uu____22817 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 g_w in
                                                        (uu____22817, g_when)) in
                                               (match uu____22726 with
                                                | (c_weak, g_when_weak) ->
                                                    let binders =
                                                      FStar_List.map
                                                        FStar_Syntax_Syntax.mk_binder
                                                        pat_bvs in
                                                    let maybe_return_c_weak
                                                      should_return =
                                                      let c_weak1 =
                                                        let uu____22857 =
                                                          should_return &&
                                                            (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                               c_weak) in
                                                        if uu____22857
                                                        then
                                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                            env branch_exp1
                                                            c_weak
                                                        else c_weak in
                                                      if
                                                        branch_has_layered_effect
                                                      then
                                                        ((let uu____22860 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects") in
                                                          if uu____22860
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
                                                                    let uu____22872
                                                                    =
                                                                    let uu____22873
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    [uu____22873] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____22872
                                                                    FStar_Range.dummyRange)) in
                                                          let pat_bv_tms2 =
                                                            let env1 =
                                                              let uu___3119_22910
                                                                =
                                                                FStar_TypeChecker_Env.push_bv
                                                                  env
                                                                  scrutinee in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___3119_22910.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              } in
                                                            let uu____22911 =
                                                              let uu____22914
                                                                =
                                                                FStar_List.fold_left2
                                                                  (fun
                                                                    uu____22942
                                                                    ->
                                                                    fun
                                                                    pat_bv_tm
                                                                    ->
                                                                    fun bv ->
                                                                    match uu____22942
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
                                                                    let uu____22983
                                                                    =
                                                                    let uu____22990
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pat_bv_tm
                                                                    (FStar_Syntax_Subst.subst
                                                                    substs) in
                                                                    let uu____22991
                                                                    =
                                                                    let uu____23002
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t in
                                                                    tc_trivial_guard
                                                                    uu____23002 in
                                                                    FStar_All.pipe_right
                                                                    uu____22990
                                                                    uu____22991 in
                                                                    FStar_All.pipe_right
                                                                    uu____22983
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
                                                                uu____22914
                                                                FStar_Pervasives_Native.snd in
                                                            FStar_All.pipe_right
                                                              uu____22911
                                                              (FStar_List.map
                                                                 (FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1)) in
                                                          (let uu____23064 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env)
                                                               (FStar_Options.Other
                                                                  "LayeredEffects") in
                                                           if uu____23064
                                                           then
                                                             let uu____23065
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun s ->
                                                                    fun t ->
                                                                    let uu____23071
                                                                    =
                                                                    let uu____23072
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23072 in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23071)
                                                                 ""
                                                                 pat_bv_tms2 in
                                                             let uu____23073
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun s ->
                                                                    fun t ->
                                                                    let uu____23079
                                                                    =
                                                                    let uu____23080
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23080 in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23079)
                                                                 "" pat_bvs in
                                                             FStar_Util.print2
                                                               "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                                                               uu____23065
                                                               uu____23073
                                                           else ());
                                                          (let uu____23082 =
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
                                                           let uu____23089 =
                                                             let uu____23094
                                                               =
                                                               FStar_TypeChecker_Env.push_bv
                                                                 env
                                                                 scrutinee in
                                                             FStar_TypeChecker_Util.close_layered_lcomp
                                                               uu____23094
                                                               pat_bvs
                                                               pat_bv_tms2 in
                                                           FStar_All.pipe_right
                                                             uu____23082
                                                             uu____23089)))
                                                      else
                                                        FStar_TypeChecker_Util.close_wp_lcomp
                                                          env pat_bvs c_weak1 in
                                                    let uu____23096 =
                                                      FStar_TypeChecker_Env.close_guard
                                                        env binders
                                                        g_when_weak in
                                                    let uu____23097 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        guard_pat g_branch1 in
                                                    ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                      (c_weak.FStar_TypeChecker_Common.cflags),
                                                      maybe_return_c_weak,
                                                      uu____23096,
                                                      uu____23097)) in
                                         match uu____22672 with
                                         | (effect_label, cflags,
                                            maybe_return_c, g_when1,
                                            g_branch1) ->
                                             let guard =
                                               FStar_TypeChecker_Env.conj_guard
                                                 g_when1 g_branch1 in
                                             ((let uu____23147 =
                                                 FStar_TypeChecker_Env.debug
                                                   env FStar_Options.High in
                                               if uu____23147
                                               then
                                                 let uu____23148 =
                                                   FStar_TypeChecker_Rel.guard_to_string
                                                     env guard in
                                                 FStar_All.pipe_left
                                                   (FStar_Util.print1
                                                      "Carrying guard from match: %s\n")
                                                   uu____23148
                                               else ());
                                              (let uu____23150 =
                                                 FStar_Syntax_Subst.close_branch
                                                   (pattern1, when_clause1,
                                                     branch_exp1) in
                                               let uu____23167 =
                                                 let uu____23168 =
                                                   FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder
                                                     pat_bvs in
                                                 FStar_TypeChecker_Util.close_guard_implicits
                                                   env false uu____23168
                                                   guard in
                                               (uu____23150, branch_guard,
                                                 effect_label, cflags,
                                                 maybe_return_c, uu____23167,
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
          let uu____23211 = check_let_bound_def true env1 lb in
          (match uu____23211 with
           | (e1, univ_vars, c1, g1, annotated) ->
               let uu____23233 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____23254 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____23254, univ_vars, c1)
                 else
                   (let g11 =
                      let uu____23259 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____23259
                        (FStar_TypeChecker_Rel.resolve_implicits env1) in
                    let uu____23260 = FStar_TypeChecker_Common.lcomp_comp c1 in
                    match uu____23260 with
                    | (comp1, g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1 in
                        let uu____23278 =
                          let uu____23291 =
                            FStar_TypeChecker_Generalize.generalize env1
                              false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)] in
                          FStar_List.hd uu____23291 in
                        (match uu____23278 with
                         | (uu____23340, univs, e11, c11, gvs) ->
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
                             let uu____23354 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11 in
                             (g14, e11, univs, uu____23354))) in
               (match uu____23233 with
                | (g11, e11, univ_vars1, c11) ->
                    let uu____23371 =
                      let uu____23380 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____23380
                      then
                        let uu____23389 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____23389 with
                        | (ok, c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____23418 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.log_issue uu____23418
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____23419 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____23419, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____23430 =
                            FStar_TypeChecker_Common.lcomp_comp c11 in
                          match uu____23430 with
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
                                  let uu____23454 =
                                    FStar_Syntax_Util.is_pure_comp c in
                                  if uu____23454
                                  then e2
                                  else
                                    ((let uu____23459 =
                                        FStar_TypeChecker_Env.get_range env1 in
                                      FStar_Errors.log_issue uu____23459
                                        FStar_TypeChecker_Err.top_level_effect);
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Masked_effect)))
                                       e2.FStar_Syntax_Syntax.pos) in
                                (e21, c))))) in
                    (match uu____23371 with
                     | (e21, c12) ->
                         ((let uu____23483 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium in
                           if uu____23483
                           then
                             let uu____23484 =
                               FStar_Syntax_Print.term_to_string e11 in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____23484
                           else ());
                          (let e12 =
                             let uu____23487 = FStar_Options.tcnorm () in
                             if uu____23487
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
                           (let uu____23490 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium in
                            if uu____23490
                            then
                              let uu____23491 =
                                FStar_Syntax_Print.term_to_string e12 in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____23491
                            else ());
                           (let cres =
                              let uu____23494 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12 in
                              if uu____23494
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
                                   | (wp, uu____23499)::[] -> wp
                                   | uu____23524 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args" in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name in
                                 let wp2 =
                                   let ret =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_return_vc_combinator in
                                   let uu____23538 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [FStar_Syntax_Syntax.U_zero] env1
                                       c1_eff_decl ret in
                                   let uu____23539 =
                                     let uu____23540 =
                                       FStar_Syntax_Syntax.as_arg
                                         FStar_Syntax_Syntax.t_unit in
                                     let uu____23549 =
                                       let uu____23560 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.unit_const in
                                       [uu____23560] in
                                     uu____23540 :: uu____23549 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____23538
                                     uu____23539 e21.FStar_Syntax_Syntax.pos in
                                 let wp =
                                   let bind =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator in
                                   let uu____23595 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       (FStar_List.append
                                          c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                          [FStar_Syntax_Syntax.U_zero]) env1
                                       c1_eff_decl bind in
                                   let uu____23596 =
                                     let uu____23597 =
                                       let uu____23606 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_constant
                                              (FStar_Const.Const_range
                                                 (lb.FStar_Syntax_Syntax.lbpos)))
                                           lb.FStar_Syntax_Syntax.lbpos in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____23606 in
                                     let uu____23615 =
                                       let uu____23626 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           c1_comp_typ.FStar_Syntax_Syntax.result_typ in
                                       let uu____23643 =
                                         let uu____23654 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.t_unit in
                                         let uu____23663 =
                                           let uu____23674 =
                                             FStar_Syntax_Syntax.as_arg c1_wp in
                                           let uu____23683 =
                                             let uu____23694 =
                                               let uu____23703 =
                                                 let uu____23704 =
                                                   let uu____23705 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       c1_comp_typ.FStar_Syntax_Syntax.result_typ in
                                                   [uu____23705] in
                                                 FStar_Syntax_Util.abs
                                                   uu____23704 wp2
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Util.mk_residual_comp
                                                         FStar_Parser_Const.effect_Tot_lid
                                                         FStar_Pervasives_Native.None
                                                         [FStar_Syntax_Syntax.TOTAL])) in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23703 in
                                             [uu____23694] in
                                           uu____23674 :: uu____23683 in
                                         uu____23654 :: uu____23663 in
                                       uu____23626 :: uu____23643 in
                                     uu____23597 :: uu____23615 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____23595
                                     uu____23596 lb.FStar_Syntax_Syntax.lbpos in
                                 let uu____23782 =
                                   let uu____23783 =
                                     let uu____23794 =
                                       FStar_Syntax_Syntax.as_arg wp in
                                     [uu____23794] in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____23783;
                                     FStar_Syntax_Syntax.flags = []
                                   } in
                                 FStar_Syntax_Syntax.mk_Comp uu____23782) in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars1
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos in
                            let uu____23822 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                e.FStar_Syntax_Syntax.pos in
                            let uu____23833 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres in
                            (uu____23822, uu____23833,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____23834 -> failwith "Impossible"
and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lem_typ ->
      fun c2 ->
        let uu____23844 = FStar_Syntax_Util.is_smt_lemma lem_typ in
        if uu____23844
        then
          let universe_of_binders bs =
            let uu____23869 =
              FStar_List.fold_left
                (fun uu____23894 ->
                   fun b ->
                     match uu____23894 with
                     | (env1, us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b] in
                         (env2, (u :: us))) (env, []) bs in
            match uu____23869 with | (uu____23942, us) -> FStar_List.rev us in
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
            let uu___3251_23974 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3251_23974.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3251_23974.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3251_23974.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3251_23974.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3251_23974.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3251_23974.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3251_23974.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3251_23974.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3251_23974.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3251_23974.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3251_23974.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3251_23974.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3251_23974.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3251_23974.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3251_23974.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3251_23974.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___3251_23974.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___3251_23974.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3251_23974.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3251_23974.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3251_23974.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3251_23974.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3251_23974.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3251_23974.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3251_23974.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3251_23974.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3251_23974.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3251_23974.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3251_23974.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3251_23974.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3251_23974.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3251_23974.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3251_23974.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3251_23974.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3251_23974.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3251_23974.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3251_23974.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3251_23974.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3251_23974.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3251_23974.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3251_23974.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3251_23974.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3251_23974.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3251_23974.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3251_23974.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___3251_23974.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let uu____23975 =
            let uu____23986 =
              let uu____23987 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____23987 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____23986 lb in
          (match uu____23975 with
           | (e1, uu____24009, c1, g1, annotated) ->
               let pure_or_ghost =
                 FStar_TypeChecker_Common.is_pure_or_ghost_lcomp c1 in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____24018 =
                     let uu____24023 =
                       let uu____24024 = FStar_Syntax_Print.term_to_string e1 in
                       let uu____24025 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____24024 uu____24025 in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____24023) in
                   FStar_Errors.raise_error uu____24018
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____24032 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ) in
                   if uu____24032
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs in
                 let x =
                   let uu___3266_24041 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3266_24041.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3266_24041.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   } in
                 let uu____24042 =
                   let uu____24047 =
                     let uu____24048 = FStar_Syntax_Syntax.mk_binder x in
                     [uu____24048] in
                   FStar_Syntax_Subst.open_term uu____24047 e2 in
                 match uu____24042 with
                 | (xb, e21) ->
                     let xbinder = FStar_List.hd xb in
                     let x1 = FStar_Pervasives_Native.fst xbinder in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1 in
                     let uu____24092 =
                       let uu____24099 = tc_term env_x e21 in
                       FStar_All.pipe_right uu____24099
                         (fun uu____24125 ->
                            match uu____24125 with
                            | (e22, c2, g2) ->
                                let uu____24141 =
                                  let uu____24146 =
                                    FStar_All.pipe_right
                                      (fun uu____24161 ->
                                         "folding guard g2 of e2 in the lcomp")
                                      (fun uu____24165 ->
                                         FStar_Pervasives_Native.Some
                                           uu____24165) in
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    uu____24146 env_x e22 c2 g2 in
                                (match uu____24141 with
                                 | (c21, g21) -> (e22, c21, g21))) in
                     (match uu____24092 with
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
                            let uu____24193 =
                              let uu____24194 =
                                let uu____24207 =
                                  FStar_Syntax_Subst.close xb e23 in
                                ((false, [lb1]), uu____24207) in
                              FStar_Syntax_Syntax.Tm_let uu____24194 in
                            FStar_Syntax_Syntax.mk uu____24193
                              e.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ in
                          let g21 =
                            let uu____24222 =
                              let uu____24223 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2) in
                              FStar_All.pipe_right uu____24223
                                (FStar_TypeChecker_Env.is_layered_effect env2) in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____24222 xb g2 in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g21 in
                          let uu____24225 =
                            let uu____24226 =
                              FStar_TypeChecker_Env.expected_typ env2 in
                            FStar_Option.isSome uu____24226 in
                          if uu____24225
                          then
                            let tt =
                              let uu____24236 =
                                FStar_TypeChecker_Env.expected_typ env2 in
                              FStar_All.pipe_right uu____24236
                                FStar_Option.get in
                            ((let uu____24242 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports") in
                              if uu____24242
                              then
                                let uu____24243 =
                                  FStar_Syntax_Print.term_to_string tt in
                                let uu____24244 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____24243 uu____24244
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____24247 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ in
                             match uu____24247 with
                             | (t, g_ex) ->
                                 ((let uu____24261 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports") in
                                   if uu____24261
                                   then
                                     let uu____24262 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ in
                                     let uu____24263 =
                                       FStar_Syntax_Print.term_to_string t in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____24262 uu____24263
                                   else ());
                                  (let uu____24265 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard in
                                   (e4,
                                     (let uu___3305_24267 = cres in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3305_24267.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3305_24267.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3305_24267.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____24265))))))))
      | uu____24268 ->
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
          let uu____24300 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____24300 with
           | (lbs1, e21) ->
               let uu____24319 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____24319 with
                | (env0, topt) ->
                    let uu____24338 = build_let_rec_env true env0 lbs1 in
                    (match uu____24338 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____24360 = check_let_recs rec_env lbs2 in
                         (match uu____24360 with
                          | (lbs3, g_lbs) ->
                              let g_lbs1 =
                                let uu____24380 =
                                  let uu____24381 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs in
                                  FStar_All.pipe_right uu____24381
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1) in
                                FStar_All.pipe_right uu____24380
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1) in
                              let all_lb_names =
                                let uu____24387 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____24387
                                  (fun uu____24404 ->
                                     FStar_Pervasives_Native.Some uu____24404) in
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
                                     let uu____24437 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb ->
                                               let uu____24471 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____24471))) in
                                     FStar_TypeChecker_Generalize.generalize
                                       env1 true uu____24437 in
                                   FStar_List.map2
                                     (fun uu____24505 ->
                                        fun lb ->
                                          match uu____24505 with
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
                                let uu____24553 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____24553 in
                              let uu____24554 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____24554 with
                               | (lbs5, e22) ->
                                   ((let uu____24574 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____24574
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____24575 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____24575, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____24586 -> failwith "Impossible"
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
          let uu____24618 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____24618 with
           | (lbs1, e21) ->
               let uu____24637 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____24637 with
                | (env0, topt) ->
                    let uu____24656 = build_let_rec_env false env0 lbs1 in
                    (match uu____24656 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____24678 =
                           let uu____24685 = check_let_recs rec_env lbs2 in
                           FStar_All.pipe_right uu____24685
                             (fun uu____24708 ->
                                match uu____24708 with
                                | (lbs3, g) ->
                                    let uu____24727 =
                                      FStar_TypeChecker_Env.conj_guard g_t g in
                                    (lbs3, uu____24727)) in
                         (match uu____24678 with
                          | (lbs3, g_lbs) ->
                              let uu____24742 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2 ->
                                        fun lb ->
                                          let x =
                                            let uu___3380_24765 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3380_24765.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3380_24765.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___3383_24767 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3383_24767.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3383_24767.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3383_24767.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3383_24767.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3383_24767.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3383_24767.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____24742 with
                               | (env2, lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____24794 = tc_term env2 e21 in
                                   (match uu____24794 with
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
                                          let uu____24818 =
                                            let uu____24819 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____24819 g2 in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____24818 in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_wp_lcomp
                                            env2 bvs cres3 in
                                        let tres =
                                          norm env2
                                            cres4.FStar_TypeChecker_Common.res_typ in
                                        let cres5 =
                                          let uu___3404_24829 = cres4 in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3404_24829.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3404_24829.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3404_24829.FStar_TypeChecker_Common.comp_thunk)
                                          } in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb ->
                                                    let uu____24837 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____24837)) in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard in
                                        let uu____24838 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____24838 with
                                         | (lbs5, e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____24876 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  let uu____24877 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  (match uu____24877 with
                                                   | (tres1, g_ex) ->
                                                       let cres6 =
                                                         let uu___3420_24891
                                                           = cres5 in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3420_24891.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3420_24891.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3420_24891.FStar_TypeChecker_Common.comp_thunk)
                                                         } in
                                                       let uu____24892 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1 in
                                                       (e, cres6,
                                                         uu____24892))))))))))
      | uu____24893 -> failwith "Impossible"
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
          let uu____24942 = FStar_Options.ml_ish () in
          if uu____24942
          then FStar_Pervasives_Native.None
          else
            (let lbtyp0 = lbtyp in
             let uu____24955 = FStar_Syntax_Util.abs_formals lbdef in
             match uu____24955 with
             | (actuals, body, body_lc) ->
                 let actuals1 =
                   let uu____24978 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____24978 actuals in
                 let nactuals = FStar_List.length actuals1 in
                 let uu____24986 =
                   FStar_TypeChecker_Normalize.get_n_binders env nactuals
                     lbtyp in
                 (match uu____24986 with
                  | (formals, c) ->
                      (if
                         (FStar_List.isEmpty formals) ||
                           (FStar_List.isEmpty actuals1)
                       then
                         (let uu____25012 =
                            let uu____25017 =
                              let uu____25018 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              let uu____25019 =
                                FStar_Syntax_Print.term_to_string lbtyp in
                              FStar_Util.format2
                                "Only function literals with arrow types can be defined recursively; got %s : %s"
                                uu____25018 uu____25019 in
                            (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                              uu____25017) in
                          FStar_Errors.raise_error uu____25012
                            lbtyp.FStar_Syntax_Syntax.pos)
                       else ();
                       (let nformals = FStar_List.length formals in
                        let uu____25022 =
                          let uu____25023 =
                            FStar_All.pipe_right
                              (FStar_Syntax_Util.comp_effect_name c)
                              (FStar_TypeChecker_Env.lookup_effect_quals env) in
                          FStar_All.pipe_right uu____25023
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect) in
                        if uu____25022
                        then
                          let uu____25036 =
                            let uu____25041 =
                              FStar_Syntax_Util.abs actuals1 body body_lc in
                            (nformals, uu____25041) in
                          FStar_Pervasives_Native.Some uu____25036
                        else FStar_Pervasives_Native.None)))) in
        let uu____25051 =
          FStar_List.fold_left
            (fun uu____25085 ->
               fun lb ->
                 match uu____25085 with
                 | (lbs1, env1, g_acc) ->
                     let uu____25110 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____25110 with
                      | (univ_vars, t, check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let uu____25130 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars in
                               let uu____25147 =
                                 let uu____25154 =
                                   let uu____25155 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____25155 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3460_25166 = env01 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3460_25166.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3460_25166.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3460_25166.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3460_25166.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3460_25166.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3460_25166.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3460_25166.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3460_25166.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3460_25166.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3460_25166.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3460_25166.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3460_25166.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3460_25166.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3460_25166.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3460_25166.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3460_25166.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___3460_25166.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3460_25166.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3460_25166.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3460_25166.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3460_25166.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3460_25166.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3460_25166.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3460_25166.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3460_25166.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3460_25166.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3460_25166.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3460_25166.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3460_25166.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3460_25166.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3460_25166.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3460_25166.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3460_25166.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3460_25166.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3460_25166.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3460_25166.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3460_25166.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3460_25166.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3460_25166.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3460_25166.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3460_25166.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3460_25166.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3460_25166.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3460_25166.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3460_25166.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___3460_25166.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }) t uu____25154 "" in
                               match uu____25147 with
                               | (t1, uu____25174, g) ->
                                   let uu____25176 =
                                     let uu____25177 =
                                       let uu____25178 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2) in
                                       FStar_All.pipe_right uu____25178
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2) in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____25177 in
                                   let uu____25179 = norm env01 t1 in
                                   (uu____25176, uu____25179)) in
                          (match uu____25130 with
                           | (g, t1) ->
                               let uu____25198 =
                                 let uu____25203 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1 in
                                 match uu____25203 with
                                 | FStar_Pervasives_Native.Some (arity, def)
                                     ->
                                     let lb1 =
                                       let uu___3473_25221 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3473_25221.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3473_25221.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = def;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3473_25221.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3473_25221.FStar_Syntax_Syntax.lbpos)
                                       } in
                                     let env3 =
                                       let uu___3476_25223 = env2 in
                                       {
                                         FStar_TypeChecker_Env.solver =
                                           (uu___3476_25223.FStar_TypeChecker_Env.solver);
                                         FStar_TypeChecker_Env.range =
                                           (uu___3476_25223.FStar_TypeChecker_Env.range);
                                         FStar_TypeChecker_Env.curmodule =
                                           (uu___3476_25223.FStar_TypeChecker_Env.curmodule);
                                         FStar_TypeChecker_Env.gamma =
                                           (uu___3476_25223.FStar_TypeChecker_Env.gamma);
                                         FStar_TypeChecker_Env.gamma_sig =
                                           (uu___3476_25223.FStar_TypeChecker_Env.gamma_sig);
                                         FStar_TypeChecker_Env.gamma_cache =
                                           (uu___3476_25223.FStar_TypeChecker_Env.gamma_cache);
                                         FStar_TypeChecker_Env.modules =
                                           (uu___3476_25223.FStar_TypeChecker_Env.modules);
                                         FStar_TypeChecker_Env.expected_typ =
                                           (uu___3476_25223.FStar_TypeChecker_Env.expected_typ);
                                         FStar_TypeChecker_Env.sigtab =
                                           (uu___3476_25223.FStar_TypeChecker_Env.sigtab);
                                         FStar_TypeChecker_Env.attrtab =
                                           (uu___3476_25223.FStar_TypeChecker_Env.attrtab);
                                         FStar_TypeChecker_Env.instantiate_imp
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.instantiate_imp);
                                         FStar_TypeChecker_Env.effects =
                                           (uu___3476_25223.FStar_TypeChecker_Env.effects);
                                         FStar_TypeChecker_Env.generalize =
                                           (uu___3476_25223.FStar_TypeChecker_Env.generalize);
                                         FStar_TypeChecker_Env.letrecs =
                                           (((lb1.FStar_Syntax_Syntax.lbname),
                                              arity, t1, univ_vars) ::
                                           (env2.FStar_TypeChecker_Env.letrecs));
                                         FStar_TypeChecker_Env.top_level =
                                           (uu___3476_25223.FStar_TypeChecker_Env.top_level);
                                         FStar_TypeChecker_Env.check_uvars =
                                           (uu___3476_25223.FStar_TypeChecker_Env.check_uvars);
                                         FStar_TypeChecker_Env.use_eq =
                                           (uu___3476_25223.FStar_TypeChecker_Env.use_eq);
                                         FStar_TypeChecker_Env.use_eq_strict
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.use_eq_strict);
                                         FStar_TypeChecker_Env.is_iface =
                                           (uu___3476_25223.FStar_TypeChecker_Env.is_iface);
                                         FStar_TypeChecker_Env.admit =
                                           (uu___3476_25223.FStar_TypeChecker_Env.admit);
                                         FStar_TypeChecker_Env.lax =
                                           (uu___3476_25223.FStar_TypeChecker_Env.lax);
                                         FStar_TypeChecker_Env.lax_universes
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.lax_universes);
                                         FStar_TypeChecker_Env.phase1 =
                                           (uu___3476_25223.FStar_TypeChecker_Env.phase1);
                                         FStar_TypeChecker_Env.failhard =
                                           (uu___3476_25223.FStar_TypeChecker_Env.failhard);
                                         FStar_TypeChecker_Env.nosynth =
                                           (uu___3476_25223.FStar_TypeChecker_Env.nosynth);
                                         FStar_TypeChecker_Env.uvar_subtyping
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.uvar_subtyping);
                                         FStar_TypeChecker_Env.tc_term =
                                           (uu___3476_25223.FStar_TypeChecker_Env.tc_term);
                                         FStar_TypeChecker_Env.type_of =
                                           (uu___3476_25223.FStar_TypeChecker_Env.type_of);
                                         FStar_TypeChecker_Env.universe_of =
                                           (uu___3476_25223.FStar_TypeChecker_Env.universe_of);
                                         FStar_TypeChecker_Env.check_type_of
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.check_type_of);
                                         FStar_TypeChecker_Env.use_bv_sorts =
                                           (uu___3476_25223.FStar_TypeChecker_Env.use_bv_sorts);
                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.qtbl_name_and_index);
                                         FStar_TypeChecker_Env.normalized_eff_names
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.normalized_eff_names);
                                         FStar_TypeChecker_Env.fv_delta_depths
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.fv_delta_depths);
                                         FStar_TypeChecker_Env.proof_ns =
                                           (uu___3476_25223.FStar_TypeChecker_Env.proof_ns);
                                         FStar_TypeChecker_Env.synth_hook =
                                           (uu___3476_25223.FStar_TypeChecker_Env.synth_hook);
                                         FStar_TypeChecker_Env.try_solve_implicits_hook
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                         FStar_TypeChecker_Env.splice =
                                           (uu___3476_25223.FStar_TypeChecker_Env.splice);
                                         FStar_TypeChecker_Env.mpreprocess =
                                           (uu___3476_25223.FStar_TypeChecker_Env.mpreprocess);
                                         FStar_TypeChecker_Env.postprocess =
                                           (uu___3476_25223.FStar_TypeChecker_Env.postprocess);
                                         FStar_TypeChecker_Env.identifier_info
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.identifier_info);
                                         FStar_TypeChecker_Env.tc_hooks =
                                           (uu___3476_25223.FStar_TypeChecker_Env.tc_hooks);
                                         FStar_TypeChecker_Env.dsenv =
                                           (uu___3476_25223.FStar_TypeChecker_Env.dsenv);
                                         FStar_TypeChecker_Env.nbe =
                                           (uu___3476_25223.FStar_TypeChecker_Env.nbe);
                                         FStar_TypeChecker_Env.strict_args_tab
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.strict_args_tab);
                                         FStar_TypeChecker_Env.erasable_types_tab
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.erasable_types_tab);
                                         FStar_TypeChecker_Env.enable_defer_to_tac
                                           =
                                           (uu___3476_25223.FStar_TypeChecker_Env.enable_defer_to_tac)
                                       } in
                                     (lb1, env3)
                                 | FStar_Pervasives_Native.None ->
                                     let lb1 =
                                       let uu___3480_25237 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3480_25237.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3480_25237.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3480_25237.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3480_25237.FStar_Syntax_Syntax.lbpos)
                                       } in
                                     let uu____25238 =
                                       FStar_TypeChecker_Env.push_let_binding
                                         env2 lb1.FStar_Syntax_Syntax.lbname
                                         (univ_vars, t1) in
                                     (lb1, uu____25238) in
                               (match uu____25198 with
                                | (lb1, env3) -> ((lb1 :: lbs1), env3, g)))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs in
        match uu____25051 with
        | (lbs1, env1, g) -> ((FStar_List.rev lbs1), env1, g)
and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun lbs ->
      let uu____25278 =
        let uu____25287 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb ->
                  let uu____25313 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____25313 with
                  | (bs, t, lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____25343 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____25343
                       | uu____25348 ->
                           let arity =
                             let uu____25351 =
                               FStar_TypeChecker_Env.get_letrec_arity env
                                 lb.FStar_Syntax_Syntax.lbname in
                             match uu____25351 with
                             | FStar_Pervasives_Native.Some n -> n
                             | FStar_Pervasives_Native.None ->
                                 FStar_List.length bs in
                           let uu____25361 = FStar_List.splitAt arity bs in
                           (match uu____25361 with
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
                                  let uu___3512_25456 = lb in
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      (uu___3512_25456.FStar_Syntax_Syntax.lbname);
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___3512_25456.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp =
                                      (uu___3512_25456.FStar_Syntax_Syntax.lbtyp);
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___3512_25456.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___3512_25456.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___3512_25456.FStar_Syntax_Syntax.lbpos)
                                  } in
                                let uu____25457 =
                                  let uu____25464 =
                                    FStar_TypeChecker_Env.set_expected_typ
                                      env lb1.FStar_Syntax_Syntax.lbtyp in
                                  tc_tot_or_gtot_term uu____25464
                                    lb1.FStar_Syntax_Syntax.lbdef in
                                (match uu____25457 with
                                 | (e, c, g) ->
                                     ((let uu____25473 =
                                         let uu____25474 =
                                           FStar_TypeChecker_Common.is_total_lcomp
                                             c in
                                         Prims.op_Negation uu____25474 in
                                       if uu____25473
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
        FStar_All.pipe_right uu____25287 FStar_List.unzip in
      match uu____25278 with
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
        let uu____25523 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____25523 with
        | (env1, uu____25541) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____25549 = check_lbtyp top_level env lb in
            (match uu____25549 with
             | (topt, wf_annot, univ_vars, univ_opening, env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____25593 =
                     tc_maybe_toplevel_term
                       (let uu___3543_25602 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3543_25602.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3543_25602.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3543_25602.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3543_25602.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3543_25602.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3543_25602.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3543_25602.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3543_25602.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3543_25602.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3543_25602.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3543_25602.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3543_25602.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3543_25602.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3543_25602.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3543_25602.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3543_25602.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___3543_25602.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3543_25602.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3543_25602.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3543_25602.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3543_25602.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3543_25602.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3543_25602.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3543_25602.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3543_25602.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3543_25602.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3543_25602.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3543_25602.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3543_25602.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3543_25602.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3543_25602.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3543_25602.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3543_25602.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3543_25602.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3543_25602.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3543_25602.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3543_25602.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3543_25602.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3543_25602.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3543_25602.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3543_25602.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3543_25602.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3543_25602.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3543_25602.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3543_25602.FStar_TypeChecker_Env.erasable_types_tab);
                          FStar_TypeChecker_Env.enable_defer_to_tac =
                            (uu___3543_25602.FStar_TypeChecker_Env.enable_defer_to_tac)
                        }) e11 in
                   match uu____25593 with
                   | (e12, c1, g1) ->
                       let uu____25616 =
                         let uu____25621 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____25626 ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____25621 e12 c1 wf_annot in
                       (match uu____25616 with
                        | (c11, guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f in
                            ((let uu____25641 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____25641
                              then
                                let uu____25642 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____25643 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11 in
                                let uu____25644 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____25642 uu____25643 uu____25644
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
            let uu____25678 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____25678 with
             | (univ_opening, univ_vars) ->
                 let uu____25711 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars,
                   univ_opening, uu____25711))
        | uu____25716 ->
            let uu____25717 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____25717 with
             | (univ_opening, univ_vars) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____25766 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars,
                     univ_opening, uu____25766)
                 else
                   (let uu____25772 = FStar_Syntax_Util.type_u () in
                    match uu____25772 with
                    | (k, uu____25792) ->
                        let uu____25793 =
                          tc_check_tot_or_gtot_term env1 t1 k "" in
                        (match uu____25793 with
                         | (t2, uu____25815, g) ->
                             ((let uu____25818 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____25818
                               then
                                 let uu____25819 =
                                   let uu____25820 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____25820 in
                                 let uu____25821 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____25819 uu____25821
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____25824 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars, univ_opening, uu____25824))))))
and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env ->
    fun uu____25830 ->
      match uu____25830 with
      | (x, imp) ->
          let uu____25857 = FStar_Syntax_Util.type_u () in
          (match uu____25857 with
           | (tu, u) ->
               ((let uu____25879 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____25879
                 then
                   let uu____25880 = FStar_Syntax_Print.bv_to_string x in
                   let uu____25881 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____25882 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____25880 uu____25881 uu____25882
                 else ());
                (let uu____25884 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu "" in
                 match uu____25884 with
                 | (t, uu____25906, g) ->
                     let uu____25908 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau_or_attr) ->
                           (match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let uu____25931 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau in
                                (match uu____25931 with
                                 | (tau1, uu____25945, g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                               tau1))), g1))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let uu____25952 =
                                  tc_check_tot_or_gtot_term env attr
                                    FStar_Syntax_Syntax.t_unit "" in
                                (match uu____25952 with
                                 | (attr1, uu____25966, g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                               attr1))),
                                       FStar_TypeChecker_Env.trivial_guard)))
                       | uu____25970 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard) in
                     (match uu____25908 with
                      | (imp1, g') ->
                          let x1 =
                            ((let uu___3613_26005 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3613_26005.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3613_26005.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1) in
                          ((let uu____26007 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High in
                            if uu____26007
                            then
                              let uu____26008 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1) in
                              let uu____26011 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____26008
                                uu____26011
                            else ());
                           (let uu____26013 = push_binding env x1 in
                            (x1, uu____26013, g, u)))))))
and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env ->
    fun bs ->
      (let uu____26025 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
       if uu____26025
       then
         let uu____26026 = FStar_Syntax_Print.binders_to_string ", " bs in
         FStar_Util.print1 "Checking binders %s\n" uu____26026
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____26135 = tc_binder env1 b in
             (match uu____26135 with
              | (b1, env', g, u) ->
                  let uu____26184 = aux env' bs2 in
                  (match uu____26184 with
                   | (bs3, env'1, g', us) ->
                       let uu____26245 =
                         let uu____26246 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g' in
                         FStar_TypeChecker_Env.conj_guard g uu____26246 in
                       ((b1 :: bs3), env'1, uu____26245, (u :: us)))) in
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
          (fun uu____26354 ->
             fun uu____26355 ->
               match (uu____26354, uu____26355) with
               | ((t, imp), (args1, g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____26447 = tc_term en1 t in
                     match uu____26447 with
                     | (t1, uu____26467, g') ->
                         let uu____26469 =
                           FStar_TypeChecker_Env.conj_guard g g' in
                         (((t1, imp) :: args1), uu____26469)))) args
          ([], FStar_TypeChecker_Env.trivial_guard) in
      FStar_List.fold_right
        (fun p ->
           fun uu____26523 ->
             match uu____26523 with
             | (pats1, g) ->
                 let uu____26550 = tc_args en p in
                 (match uu____26550 with
                  | (args, g') ->
                      let uu____26563 = FStar_TypeChecker_Env.conj_guard g g' in
                      ((args :: pats1), uu____26563))) pats
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
        let uu____26577 = tc_maybe_toplevel_term env e in
        match uu____26577 with
        | (e1, c, g) ->
            let uu____26593 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c in
            if uu____26593
            then (e1, c, g)
            else
              (let g1 =
                 FStar_TypeChecker_Rel.solve_deferred_constraints env g in
               let uu____26602 = FStar_TypeChecker_Common.lcomp_comp c in
               match uu____26602 with
               | (c1, g_c) ->
                   let c2 = norm_c env c1 in
                   let uu____26616 =
                     let uu____26621 =
                       FStar_TypeChecker_Util.is_pure_effect env
                         (FStar_Syntax_Util.comp_effect_name c2) in
                     if uu____26621
                     then
                       let uu____26626 =
                         FStar_Syntax_Syntax.mk_Total
                           (FStar_Syntax_Util.comp_result c2) in
                       (uu____26626, false)
                     else
                       (let uu____26628 =
                          FStar_Syntax_Syntax.mk_GTotal
                            (FStar_Syntax_Util.comp_result c2) in
                        (uu____26628, true)) in
                   (match uu____26616 with
                    | (target_comp, allow_ghost) ->
                        let uu____26637 =
                          FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                        (match uu____26637 with
                         | FStar_Pervasives_Native.Some g' ->
                             let uu____26647 =
                               FStar_TypeChecker_Common.lcomp_of_comp
                                 target_comp in
                             let uu____26648 =
                               let uu____26649 =
                                 FStar_TypeChecker_Env.conj_guard g_c g' in
                               FStar_TypeChecker_Env.conj_guard g1
                                 uu____26649 in
                             (e1, uu____26647, uu____26648)
                         | uu____26650 ->
                             if allow_ghost
                             then
                               let uu____26659 =
                                 FStar_TypeChecker_Err.expected_ghost_expression
                                   e1 c2 msg in
                               FStar_Errors.raise_error uu____26659
                                 e1.FStar_Syntax_Syntax.pos
                             else
                               (let uu____26671 =
                                  FStar_TypeChecker_Err.expected_pure_expression
                                    e1 c2 msg in
                                FStar_Errors.raise_error uu____26671
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
      let uu____26697 = tc_tot_or_gtot_term env t in
      match uu____26697 with
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
        let uu____26727 = tc_check_tot_or_gtot_term env t k "" in
        match uu____26727 with
        | (t1, uu____26735, g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      (let uu____26755 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____26755
       then
         let uu____26756 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____26756
       else ());
      (let env1 =
         let uu___3709_26759 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3709_26759.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3709_26759.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3709_26759.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3709_26759.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3709_26759.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3709_26759.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3709_26759.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3709_26759.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3709_26759.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3709_26759.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3709_26759.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3709_26759.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3709_26759.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3709_26759.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3709_26759.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___3709_26759.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___3709_26759.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3709_26759.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3709_26759.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3709_26759.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3709_26759.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3709_26759.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3709_26759.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3709_26759.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3709_26759.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3709_26759.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3709_26759.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3709_26759.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3709_26759.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3709_26759.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3709_26759.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3709_26759.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3709_26759.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3709_26759.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3709_26759.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3709_26759.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3709_26759.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3709_26759.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3709_26759.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3709_26759.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3709_26759.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3709_26759.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3709_26759.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3709_26759.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___3709_26759.FStar_TypeChecker_Env.enable_defer_to_tac)
         } in
       let uu____26768 =
         try
           (fun uu___3713_26782 ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1, msg, uu____26803) ->
             let uu____26804 = FStar_TypeChecker_Env.get_range env1 in
             FStar_Errors.raise_error (e1, msg) uu____26804 in
       match uu____26768 with
       | (t, c, g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c in
           let uu____26821 = FStar_TypeChecker_Common.is_total_lcomp c1 in
           if uu____26821
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____26829 =
                let uu____26834 =
                  let uu____26835 = FStar_Syntax_Print.term_to_string e in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____26835 in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____26834) in
              let uu____26836 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____26829 uu____26836))
let level_of_type_fail :
  'uuuuuu26851 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'uuuuuu26851
  =
  fun env ->
    fun e ->
      fun t ->
        let uu____26867 =
          let uu____26872 =
            let uu____26873 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____26873 t in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____26872) in
        let uu____26874 = FStar_TypeChecker_Env.get_range env in
        FStar_Errors.raise_error uu____26867 uu____26874
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      fun t ->
        let rec aux retry t1 =
          let uu____26905 =
            let uu____26906 = FStar_Syntax_Util.unrefine t1 in
            uu____26906.FStar_Syntax_Syntax.n in
          match uu____26905 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____26910 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1 in
                aux false t2
              else
                (let uu____26913 = FStar_Syntax_Util.type_u () in
                 match uu____26913 with
                 | (t_u, u) ->
                     let env1 =
                       let uu___3745_26921 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3745_26921.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3745_26921.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3745_26921.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3745_26921.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3745_26921.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3745_26921.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3745_26921.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3745_26921.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3745_26921.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3745_26921.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3745_26921.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3745_26921.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3745_26921.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3745_26921.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3745_26921.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3745_26921.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3745_26921.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3745_26921.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3745_26921.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3745_26921.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3745_26921.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3745_26921.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3745_26921.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3745_26921.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3745_26921.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3745_26921.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3745_26921.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3745_26921.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3745_26921.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3745_26921.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3745_26921.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3745_26921.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3745_26921.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3745_26921.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3745_26921.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3745_26921.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3745_26921.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3745_26921.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3745_26921.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3745_26921.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3745_26921.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3745_26921.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3745_26921.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3745_26921.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3745_26921.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3745_26921.FStar_TypeChecker_Env.enable_defer_to_tac)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____26925 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____26925
                       | uu____26926 ->
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
      let uu____26941 =
        let uu____26942 = FStar_Syntax_Subst.compress e in
        uu____26942.FStar_Syntax_Syntax.n in
      match uu____26941 with
      | FStar_Syntax_Syntax.Tm_bvar uu____26945 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____26946 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____26961 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs, t, uu____26977) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t, uu____27021) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____27028 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____27028 with | ((uu____27037, t), uu____27039) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____27045 = FStar_Syntax_Util.unfold_lazy i in
          universe_of_aux env uu____27045
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27048, (FStar_Util.Inl t, uu____27050), uu____27051) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27098, (FStar_Util.Inr c, uu____27100), uu____27101) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____27149 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____27158;
             FStar_Syntax_Syntax.vars = uu____27159;_},
           us)
          ->
          let uu____27165 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____27165 with
           | ((us', t), uu____27176) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____27182 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____27182)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____27200 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____27201 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x, uu____27209) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____27236 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____27236 with
           | (bs1, c1) ->
               let us =
                 FStar_List.map
                   (fun uu____27256 ->
                      match uu____27256 with
                      | (b, uu____27264) ->
                          let uu____27269 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____27269) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____27274 = universe_of_aux env res in
                 level_of_type env res uu____27274 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____27382 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____27397 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____27426 ->
                let uu____27427 = universe_of_aux env hd2 in
                (uu____27427, args1)
            | FStar_Syntax_Syntax.Tm_name uu____27438 ->
                let uu____27439 = universe_of_aux env hd2 in
                (uu____27439, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____27450 ->
                let uu____27463 = universe_of_aux env hd2 in
                (uu____27463, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____27474 ->
                let uu____27481 = universe_of_aux env hd2 in
                (uu____27481, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____27492 ->
                let uu____27519 = universe_of_aux env hd2 in
                (uu____27519, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____27530 ->
                let uu____27537 = universe_of_aux env hd2 in
                (uu____27537, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____27548 ->
                let uu____27549 = universe_of_aux env hd2 in
                (uu____27549, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____27560 ->
                let uu____27575 = universe_of_aux env hd2 in
                (uu____27575, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____27586 ->
                let uu____27593 = universe_of_aux env hd2 in
                (uu____27593, args1)
            | FStar_Syntax_Syntax.Tm_type uu____27604 ->
                let uu____27605 = universe_of_aux env hd2 in
                (uu____27605, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____27616, hd3::uu____27618) ->
                let uu____27683 = FStar_Syntax_Subst.open_branch hd3 in
                (match uu____27683 with
                 | (uu____27698, uu____27699, hd4) ->
                     let uu____27717 = FStar_Syntax_Util.head_and_args hd4 in
                     (match uu____27717 with
                      | (hd5, args') ->
                          type_of_head retry hd5
                            (FStar_List.append args' args1)))
            | uu____27782 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e in
                let uu____27784 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____27784 with
                 | (hd3, args2) -> type_of_head false hd3 args2)
            | uu____27841 ->
                let uu____27842 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____27842 with
                 | (env1, uu____27864) ->
                     let env2 =
                       let uu___3906_27870 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3906_27870.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3906_27870.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3906_27870.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3906_27870.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3906_27870.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3906_27870.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3906_27870.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3906_27870.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3906_27870.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3906_27870.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3906_27870.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3906_27870.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3906_27870.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3906_27870.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3906_27870.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3906_27870.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3906_27870.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3906_27870.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3906_27870.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3906_27870.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3906_27870.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3906_27870.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3906_27870.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3906_27870.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3906_27870.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3906_27870.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3906_27870.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3906_27870.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3906_27870.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3906_27870.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3906_27870.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3906_27870.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3906_27870.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3906_27870.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3906_27870.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3906_27870.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3906_27870.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3906_27870.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3906_27870.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3906_27870.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3906_27870.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3906_27870.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3906_27870.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3906_27870.FStar_TypeChecker_Env.enable_defer_to_tac)
                       } in
                     ((let uu____27872 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____27872
                       then
                         let uu____27873 =
                           let uu____27874 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____27874 in
                         let uu____27875 =
                           FStar_Syntax_Print.term_to_string hd2 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____27873 uu____27875
                       else ());
                      (let uu____27877 = tc_term env2 hd2 in
                       match uu____27877 with
                       | (uu____27898,
                          { FStar_TypeChecker_Common.eff_name = uu____27899;
                            FStar_TypeChecker_Common.res_typ = t;
                            FStar_TypeChecker_Common.cflags = uu____27901;
                            FStar_TypeChecker_Common.comp_thunk = uu____27902;_},
                          g) ->
                           ((let uu____27920 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____27920
                               (fun uu____27921 -> ()));
                            (t, args1))))) in
          let uu____27932 = type_of_head true hd args in
          (match uu____27932 with
           | (t, args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t in
               let uu____27970 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____27970 with
                | (bs, res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst res1
                    else
                      (let uu____27996 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____27996)))
      | FStar_Syntax_Syntax.Tm_match (uu____27997, hd::uu____27999) ->
          let uu____28064 = FStar_Syntax_Subst.open_branch hd in
          (match uu____28064 with
           | (uu____28065, uu____28066, hd1) -> universe_of_aux env hd1)
      | FStar_Syntax_Syntax.Tm_match (uu____28084, []) ->
          level_of_type_fail env e "empty match cases"
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      (let uu____28130 = FStar_TypeChecker_Env.debug env FStar_Options.High in
       if uu____28130
       then
         let uu____28131 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Calling universe_of_aux with %s\n" uu____28131
       else ());
      (let r = universe_of_aux env e in
       (let uu____28135 = FStar_TypeChecker_Env.debug env FStar_Options.High in
        if uu____28135
        then
          let uu____28136 = FStar_Syntax_Print.term_to_string r in
          FStar_Util.print1 "Got result from universe_of_aux = %s\n"
            uu____28136
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
      let uu____28160 = tc_binders env0 tps in
      match uu____28160 with
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
      | FStar_Syntax_Syntax.Tm_delayed uu____28217 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____28234 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____28239 = FStar_Syntax_Util.unfold_lazy i in
          type_of_well_typed_term env uu____28239
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____28241 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____28241
            (fun uu____28255 ->
               match uu____28255 with
               | (t2, uu____28263) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____28265;
             FStar_Syntax_Syntax.vars = uu____28266;_},
           us)
          ->
          let uu____28272 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____28272
            (fun uu____28286 ->
               match uu____28286 with
               | (t2, uu____28294) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____28295) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____28297 = tc_constant env t1.FStar_Syntax_Syntax.pos sc in
          FStar_Pervasives_Native.Some uu____28297
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____28299 = mk_tm_type (FStar_Syntax_Syntax.U_succ u) in
          FStar_Pervasives_Native.Some uu____28299
      | FStar_Syntax_Syntax.Tm_abs
          (bs, body, FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____28304;_})
          ->
          let mk_comp =
            let uu____28348 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid in
            if uu____28348
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____28376 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid in
               if uu____28376
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None) in
          FStar_Util.bind_opt mk_comp
            (fun f ->
               let uu____28443 = universe_of_well_typed_term env tbody in
               FStar_Util.bind_opt uu____28443
                 (fun u ->
                    let uu____28451 =
                      let uu____28454 =
                        let uu____28455 =
                          let uu____28470 =
                            f tbody (FStar_Pervasives_Native.Some u) in
                          (bs, uu____28470) in
                        FStar_Syntax_Syntax.Tm_arrow uu____28455 in
                      FStar_Syntax_Syntax.mk uu____28454
                        t1.FStar_Syntax_Syntax.pos in
                    FStar_Pervasives_Native.Some uu____28451))
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____28507 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____28507 with
           | (bs1, c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____28566 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1) in
                     FStar_Util.bind_opt uu____28566
                       (fun uc ->
                          let uu____28574 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us)) in
                          FStar_Pervasives_Native.Some uu____28574)
                 | (x, imp)::bs3 ->
                     let uu____28600 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort in
                     FStar_Util.bind_opt uu____28600
                       (fun u_x ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x in
                          aux env2 (u_x :: us) bs3) in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____28609 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x, uu____28629) ->
          let uu____28634 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort in
          FStar_Util.bind_opt uu____28634
            (fun u_x ->
               let uu____28642 = mk_tm_type u_x in
               FStar_Pervasives_Native.Some uu____28642)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____28647;
             FStar_Syntax_Syntax.vars = uu____28648;_},
           a::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____28727 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____28727 with
           | (unary_op, uu____28747) ->
               let head =
                 let uu____28775 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____28775 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____28823;
             FStar_Syntax_Syntax.vars = uu____28824;_},
           a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____28920 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____28920 with
           | (unary_op, uu____28940) ->
               let head =
                 let uu____28968 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   uu____28968 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____29024;
             FStar_Syntax_Syntax.vars = uu____29025;_},
           uu____29026::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____29065;
             FStar_Syntax_Syntax.vars = uu____29066;_},
           (t2, uu____29068)::uu____29069::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd, args) ->
          let t_hd = type_of_well_typed_term env hd in
          let rec aux t_hd1 =
            let uu____29165 =
              let uu____29166 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1 in
              uu____29166.FStar_Syntax_Syntax.n in
            match uu____29165 with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let n_args = FStar_List.length args in
                let n_bs = FStar_List.length bs in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____29238 = FStar_Util.first_N n_args bs in
                    match uu____29238 with
                    | (bs1, rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            t_hd1.FStar_Syntax_Syntax.pos in
                        let uu____29326 =
                          let uu____29331 = FStar_Syntax_Syntax.mk_Total t2 in
                          FStar_Syntax_Subst.open_comp bs1 uu____29331 in
                        (match uu____29326 with
                         | (bs2, c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____29383 = FStar_Syntax_Subst.open_comp bs c in
                       match uu____29383 with
                       | (bs1, c1) ->
                           let uu____29404 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1 in
                           if uu____29404
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____29482 ->
                     match uu____29482 with
                     | (bs1, t2) ->
                         let subst =
                           FStar_List.map2
                             (fun b ->
                                fun a ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args in
                         let uu____29558 = FStar_Syntax_Subst.subst subst t2 in
                         FStar_Pervasives_Native.Some uu____29558)
            | FStar_Syntax_Syntax.Tm_refine (x, uu____29560) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____29566, uu____29567)
                -> aux t2
            | uu____29608 -> FStar_Pervasives_Native.None in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29609, (FStar_Util.Inl t2, uu____29611), uu____29612) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29659, (FStar_Util.Inr c, uu____29661), uu____29662) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____29727 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
          FStar_Pervasives_Native.Some uu____29727
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____29735) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____29740 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____29763 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____29776 ->
          FStar_Pervasives_Native.None
and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let uu____29787 = type_of_well_typed_term env t in
      match uu____29787 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____29793;
            FStar_Syntax_Syntax.vars = uu____29794;_}
          -> FStar_Pervasives_Native.Some u
      | uu____29797 -> FStar_Pervasives_Native.None
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
            let uu___4190_29822 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4190_29822.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4190_29822.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4190_29822.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4190_29822.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4190_29822.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4190_29822.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4190_29822.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4190_29822.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4190_29822.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4190_29822.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4190_29822.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4190_29822.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4190_29822.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4190_29822.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4190_29822.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4190_29822.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4190_29822.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4190_29822.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4190_29822.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4190_29822.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4190_29822.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4190_29822.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4190_29822.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4190_29822.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4190_29822.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4190_29822.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4190_29822.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4190_29822.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4190_29822.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4190_29822.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4190_29822.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4190_29822.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4190_29822.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4190_29822.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4190_29822.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4190_29822.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4190_29822.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4190_29822.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4190_29822.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4190_29822.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4190_29822.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4190_29822.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4190_29822.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4190_29822.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4190_29822.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4190_29822.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let slow_check uu____29828 =
            if must_total
            then
              let uu____29829 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____29829 with | (uu____29836, uu____29837, g) -> g
            else
              (let uu____29840 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____29840 with | (uu____29847, uu____29848, g) -> g) in
          let uu____29850 = type_of_well_typed_term env2 t in
          match uu____29850 with
          | FStar_Pervasives_Native.None -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____29855 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits") in
                if uu____29855
                then
                  let uu____29856 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                  let uu____29857 = FStar_Syntax_Print.term_to_string t in
                  let uu____29858 = FStar_Syntax_Print.term_to_string k' in
                  let uu____29859 = FStar_Syntax_Print.term_to_string k in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____29856 uu____29857 uu____29858 uu____29859
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k in
                (let uu____29865 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits") in
                 if uu____29865
                 then
                   let uu____29866 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                   let uu____29867 = FStar_Syntax_Print.term_to_string t in
                   let uu____29868 = FStar_Syntax_Print.term_to_string k' in
                   let uu____29869 = FStar_Syntax_Print.term_to_string k in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____29866
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____29867 uu____29868 uu____29869
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
            let uu___4221_29895 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4221_29895.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4221_29895.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4221_29895.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4221_29895.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4221_29895.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4221_29895.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4221_29895.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4221_29895.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4221_29895.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4221_29895.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4221_29895.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4221_29895.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4221_29895.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4221_29895.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4221_29895.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4221_29895.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4221_29895.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4221_29895.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4221_29895.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4221_29895.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4221_29895.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4221_29895.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4221_29895.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4221_29895.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4221_29895.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4221_29895.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4221_29895.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4221_29895.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4221_29895.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4221_29895.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4221_29895.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4221_29895.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4221_29895.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4221_29895.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4221_29895.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4221_29895.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4221_29895.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4221_29895.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4221_29895.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4221_29895.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4221_29895.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4221_29895.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4221_29895.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4221_29895.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4221_29895.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4221_29895.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let slow_check uu____29901 =
            if must_total
            then
              let uu____29902 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____29902 with | (uu____29909, uu____29910, g) -> g
            else
              (let uu____29913 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____29913 with | (uu____29920, uu____29921, g) -> g) in
          let uu____29923 =
            let uu____29924 = FStar_Options.__temp_fast_implicits () in
            FStar_All.pipe_left Prims.op_Negation uu____29924 in
          if uu____29923
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k