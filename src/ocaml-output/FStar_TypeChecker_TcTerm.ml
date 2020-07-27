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
                                          (c1.FStar_TypeChecker_Common.eff_name),
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
                                      (FStar_TypeChecker_Env.is_total_effect
                                         env1 ef)
                                        ||
                                        (let uu____7289 =
                                           FStar_All.pipe_right ef
                                             (FStar_TypeChecker_Env.norm_eff_name
                                                env1) in
                                         FStar_All.pipe_right uu____7289
                                           (FStar_TypeChecker_Env.is_layered_effect
                                              env1)) in
                                    if uu____7287
                                    then
                                      let uu____7290 =
                                        FStar_Syntax_Syntax.mk_Total repr in
                                      FStar_All.pipe_right uu____7290
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
                                       let uu____7301 =
                                         FStar_Syntax_Syntax.mk_Comp ct in
                                       FStar_All.pipe_right uu____7301
                                         FStar_TypeChecker_Common.lcomp_of_comp) in
                                  let uu____7302 =
                                    comp_check_expected_typ env1 e3 c2 in
                                  match uu____7302 with
                                  | (e4, c3, g') ->
                                      let uu____7318 =
                                        let uu____7319 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g' in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7319 in
                                      (e4, c3, uu____7318))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7321;
              FStar_Syntax_Syntax.vars = uu____7322;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7366 =
               let uu____7367 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l in
               Prims.op_Negation uu____7367 in
             if uu____7366
             then
               let uu____7368 =
                 let uu____7373 =
                   let uu____7374 = FStar_Ident.string_of_lid l in
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     uu____7374 in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7373) in
               FStar_Errors.raise_error uu____7368 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7376 = FStar_Syntax_Util.head_and_args top in
             match uu____7376 with
             | (reflect_op, uu____7400) ->
                 let uu____7425 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____7425 with
                  | FStar_Pervasives_Native.None ->
                      let uu____7446 =
                        let uu____7451 =
                          let uu____7452 = FStar_Ident.string_of_lid l in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7452 in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7451) in
                      FStar_Errors.raise_error uu____7446
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                      let uu____7471 =
                        FStar_TypeChecker_Env.clear_expected_typ env1 in
                      (match uu____7471 with
                       | (env_no_ex, uu____7485) ->
                           let uu____7490 =
                             let uu____7499 =
                               tc_tot_or_gtot_term env_no_ex e1 in
                             match uu____7499 with
                             | (e2, c, g) ->
                                 ((let uu____7518 =
                                     let uu____7519 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7519 in
                                   if uu____7518
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g)) in
                           (match uu____7490 with
                            | (e2, c_e, g_e) ->
                                let uu____7548 =
                                  let uu____7563 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____7563 with
                                  | (a, u_a) ->
                                      let uu____7584 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a in
                                      (match uu____7584 with
                                       | (a_uvar, uu____7612, g_a) ->
                                           let uu____7626 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar in
                                           (uu____7626, u_a, a_uvar, g_a)) in
                                (match uu____7548 with
                                 | ((expected_repr_typ, g_repr), u_a, a, g_a)
                                     ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ in
                                     let eff_args =
                                       let uu____7668 =
                                         let uu____7669 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ in
                                         uu____7669.FStar_Syntax_Syntax.n in
                                       match uu____7668 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7682, uu____7683::args) ->
                                           args
                                       | uu____7725 ->
                                           let uu____7726 =
                                             let uu____7731 =
                                               let uu____7732 =
                                                 FStar_Ident.string_of_lid l in
                                               let uu____7733 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ in
                                               let uu____7734 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____7732 uu____7733
                                                 uu____7734 in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____7731) in
                                           FStar_Errors.raise_error
                                             uu____7726
                                             top.FStar_Syntax_Syntax.pos in
                                     let c =
                                       let uu____7746 =
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
                                       FStar_All.pipe_right uu____7746
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         top.FStar_Syntax_Syntax.pos in
                                     let uu____7782 =
                                       comp_check_expected_typ env1 e3 c in
                                     (match uu____7782 with
                                      | (e4, c1, g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_TypeChecker_Common.eff_name),
                                                        (c1.FStar_TypeChecker_Common.res_typ)))))
                                              e4.FStar_Syntax_Syntax.pos in
                                          let uu____7805 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g'] in
                                          (e5, c1, uu____7805))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head, (tau, FStar_Pervasives_Native.None)::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7844 = FStar_Syntax_Util.head_and_args top in
           (match uu____7844 with
            | (head1, args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head,
            (uu____7894, FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____7895))::(tau,
                                                          FStar_Pervasives_Native.None)::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7947 = FStar_Syntax_Util.head_and_args top in
           (match uu____7947 with
            | (head1, args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head, args) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8022 =
             match args with
             | (tau, FStar_Pervasives_Native.None)::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau, FStar_Pervasives_Native.None)::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8231 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos in
           (match uu____8022 with
            | (args1, args2) ->
                let t1 = FStar_Syntax_Util.mk_app head args1 in
                let t2 = FStar_Syntax_Util.mk_app t1 args2 in tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head, args) ->
           let env0 = env1 in
           let env2 =
             let uu____8348 =
               let uu____8349 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____8349 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____8348 instantiate_both in
           ((let uu____8365 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____8365
             then
               let uu____8366 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____8367 = FStar_Syntax_Print.term_to_string top in
               let uu____8368 =
                 let uu____8369 = FStar_TypeChecker_Env.expected_typ env0 in
                 FStar_All.pipe_right uu____8369
                   (fun uu___3_8375 ->
                      match uu___3_8375 with
                      | FStar_Pervasives_Native.None -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t) in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8366
                 uu____8367 uu____8368
             else ());
            (let uu____8380 = tc_term (no_inst env2) head in
             match uu____8380 with
             | (head1, chead, g_head) ->
                 let uu____8396 =
                   let uu____8401 = FStar_TypeChecker_Common.lcomp_comp chead in
                   FStar_All.pipe_right uu____8401
                     (fun uu____8418 ->
                        match uu____8418 with
                        | (c, g) ->
                            let uu____8429 =
                              FStar_TypeChecker_Env.conj_guard g_head g in
                            (c, uu____8429)) in
                 (match uu____8396 with
                  | (chead1, g_head1) ->
                      let uu____8438 =
                        let uu____8445 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8447 = FStar_Options.lax () in
                              Prims.op_Negation uu____8447))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head1) in
                        if uu____8445
                        then
                          let uu____8454 =
                            let uu____8461 =
                              FStar_TypeChecker_Env.expected_typ env0 in
                            check_short_circuit_args env2 head1 chead1
                              g_head1 args uu____8461 in
                          match uu____8454 with | (e1, c, g) -> (e1, c, g)
                        else
                          (let uu____8474 =
                             FStar_TypeChecker_Env.expected_typ env0 in
                           check_application_args env2 head1 chead1 g_head1
                             args uu____8474) in
                      (match uu____8438 with
                       | (e1, c, g) ->
                           let uu____8486 =
                             let uu____8493 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c in
                             if uu____8493
                             then
                               let uu____8500 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ in
                               match uu____8500 with
                               | (e2, res_typ, implicits) ->
                                   let uu____8516 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ in
                                   (e2, uu____8516, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard) in
                           (match uu____8486 with
                            | (e2, c1, implicits) ->
                                ((let uu____8528 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme in
                                  if uu____8528
                                  then
                                    let uu____8529 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8529
                                  else ());
                                 (let uu____8531 =
                                    comp_check_expected_typ env0 e2 c1 in
                                  match uu____8531 with
                                  | (e3, c2, g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits in
                                      ((let uu____8550 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme in
                                        if uu____8550
                                        then
                                          let uu____8551 =
                                            FStar_Syntax_Print.term_to_string
                                              e3 in
                                          let uu____8552 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1 in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8551 uu____8552
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8554 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8577;
               FStar_Syntax_Syntax.lbunivs = uu____8578;
               FStar_Syntax_Syntax.lbtyp = uu____8579;
               FStar_Syntax_Syntax.lbeff = uu____8580;
               FStar_Syntax_Syntax.lbdef = uu____8581;
               FStar_Syntax_Syntax.lbattrs = uu____8582;
               FStar_Syntax_Syntax.lbpos = uu____8583;_}::[]),
            uu____8584)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false, uu____8607), uu____8608) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8623;
               FStar_Syntax_Syntax.lbunivs = uu____8624;
               FStar_Syntax_Syntax.lbtyp = uu____8625;
               FStar_Syntax_Syntax.lbeff = uu____8626;
               FStar_Syntax_Syntax.lbdef = uu____8627;
               FStar_Syntax_Syntax.lbattrs = uu____8628;
               FStar_Syntax_Syntax.lbpos = uu____8629;_}::uu____8630),
            uu____8631)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true, uu____8656), uu____8657) ->
           check_inner_let_rec env1 top)
and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      let uu____8680 =
        let uu____8681 = FStar_Syntax_Subst.compress top in
        uu____8681.FStar_Syntax_Syntax.n in
      match uu____8680 with
      | FStar_Syntax_Syntax.Tm_match (e1, eqns) ->
          let uu____8728 = FStar_TypeChecker_Env.clear_expected_typ env in
          (match uu____8728 with
           | (env1, topt) ->
               let env11 = instantiate_both env1 in
               let uu____8748 = tc_term env11 e1 in
               (match uu____8748 with
                | (e11, c1, g1) ->
                    let uu____8764 =
                      let uu____8775 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1 in
                      match uu____8775 with
                      | FStar_Pervasives_Native.Some (e12, c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None -> (e11, c1, eqns) in
                    (match uu____8764 with
                     | (e12, c11, eqns1) ->
                         let eqns2 = eqns1 in
                         let uu____8830 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None ->
                               let uu____8844 = FStar_Syntax_Util.type_u () in
                               (match uu____8844 with
                                | (k, uu____8856) ->
                                    let uu____8857 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k in
                                    (match uu____8857 with
                                     | (res_t, uu____8877, g) ->
                                         let uu____8891 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t in
                                         let uu____8892 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g in
                                         (uu____8891, res_t, uu____8892))) in
                         (match uu____8830 with
                          | (env_branches, res_t, g11) ->
                              ((let uu____8903 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme in
                                if uu____8903
                                then
                                  let uu____8904 =
                                    FStar_Syntax_Print.term_to_string res_t in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____8904
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
                                let uu____9003 =
                                  let uu____9010 =
                                    FStar_List.fold_right
                                      (fun uu____9097 ->
                                         fun uu____9098 ->
                                           match (uu____9097, uu____9098)
                                           with
                                           | ((branch, f, eff_label, cflags,
                                               c, g, erasable_branch),
                                              (caccum, gaccum, erasable)) ->
                                               let uu____9348 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9348,
                                                 (erasable || erasable_branch)))
                                      t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false) in
                                  match uu____9010 with
                                  | (cases, g, erasable) ->
                                      let uu____9449 =
                                        FStar_TypeChecker_Util.bind_cases env
                                          res_t cases guard_x in
                                      (uu____9449, g, erasable) in
                                match uu____9003 with
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
                                        let uu____9465 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9465
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____9602 ->
                                                  match uu____9602 with
                                                  | ((pat, wopt, br),
                                                     uu____9648, eff_label,
                                                     uu____9650, uu____9651,
                                                     uu____9652, uu____9653)
                                                      ->
                                                      let uu____9688 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t in
                                                      (pat, wopt, uu____9688))) in
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
                                      let uu____9755 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name in
                                      if uu____9755
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____9760 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x in
                                           mk_match uu____9760 in
                                         let lb =
                                           let uu____9764 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____9764 e12 []
                                             e12.FStar_Syntax_Syntax.pos in
                                         let e =
                                           let uu____9770 =
                                             let uu____9771 =
                                               let uu____9784 =
                                                 let uu____9787 =
                                                   let uu____9788 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       guard_x in
                                                   [uu____9788] in
                                                 FStar_Syntax_Subst.close
                                                   uu____9787 e_match in
                                               ((false, [lb]), uu____9784) in
                                             FStar_Syntax_Syntax.Tm_let
                                               uu____9771 in
                                           FStar_Syntax_Syntax.mk uu____9770
                                             top.FStar_Syntax_Syntax.pos in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ) in
                                    ((let uu____9818 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme in
                                      if uu____9818
                                      then
                                        let uu____9819 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos in
                                        let uu____9820 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1 in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____9819 uu____9820
                                      else ());
                                     (let uu____9822 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches in
                                      (e, cres1, uu____9822)))))))))
      | uu____9823 ->
          let uu____9824 =
            let uu____9825 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format1 "tc_match called on %s\n" uu____9825 in
          failwith uu____9824
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
          let uu____9848 =
            match args with
            | (tau, FStar_Pervasives_Native.None)::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9887))::(tau, FStar_Pervasives_Native.None)::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9927 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng in
          match uu____9848 with
          | (tau, atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None ->
                    let uu____9958 = FStar_TypeChecker_Env.expected_typ env in
                    (match uu____9958 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None ->
                         let uu____9962 = FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9962) in
              let uu____9963 =
                let uu____9970 =
                  let uu____9971 =
                    let uu____9972 = FStar_Syntax_Util.type_u () in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9972 in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9971 in
                tc_term uu____9970 typ in
              (match uu____9963 with
               | (typ1, uu____9988, g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9991 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau in
                     match uu____9991 with
                     | (tau1, uu____10005, g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1342_10010 = tau1 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1342_10010.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1342_10010.FStar_Syntax_Syntax.vars)
                                }) in
                           (let uu____10012 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac") in
                            if uu____10012
                            then
                              let uu____10013 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print1 "Got %s\n" uu____10013
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10016 =
                              let uu____10017 =
                                FStar_Syntax_Syntax.mk_Total typ1 in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10017 in
                            (t, uu____10016,
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
            let uu___1352_10023 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1352_10023.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1352_10023.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1352_10023.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1352_10023.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1352_10023.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1352_10023.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1352_10023.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1352_10023.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1352_10023.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1352_10023.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1352_10023.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1352_10023.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1352_10023.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1352_10023.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1352_10023.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1352_10023.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1352_10023.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1352_10023.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1352_10023.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1352_10023.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1352_10023.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1352_10023.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1352_10023.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1352_10023.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1352_10023.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1352_10023.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1352_10023.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1352_10023.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1352_10023.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1352_10023.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1352_10023.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1352_10023.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1352_10023.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1352_10023.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1352_10023.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1352_10023.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1352_10023.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1352_10023.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1352_10023.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1352_10023.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1352_10023.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1352_10023.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1352_10023.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1352_10023.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1352_10023.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___1352_10023.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let uu____10024 = FStar_Syntax_Syntax.t_tac_of a b in
          tc_check_tot_or_gtot_term env1 tau uu____10024 ""
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
          let uu____10046 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic in
          (match uu____10046 with
           | (tactic1, uu____10060, g) ->
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
        let uu____10113 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____10113 with
        | (e2, t1, implicits) ->
            let tc =
              let uu____10134 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____10134
              then FStar_Util.Inl t1
              else
                (let uu____10140 =
                   let uu____10141 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____10141 in
                 FStar_Util.Inr uu____10140) in
            let is_data_ctor uu___4_10149 =
              match uu___4_10149 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10152) -> true
              | uu____10159 -> false in
            let uu____10162 =
              (is_data_ctor dc) &&
                (let uu____10164 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____10164) in
            if uu____10162
            then
              let uu____10171 =
                let uu____10176 =
                  let uu____10177 =
                    FStar_Ident.string_of_lid v.FStar_Syntax_Syntax.v in
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    uu____10177 in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10176) in
              let uu____10178 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____10171 uu____10178
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10195 =
            let uu____10200 =
              let uu____10201 = FStar_Syntax_Print.term_to_string top in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10201 in
            (FStar_Errors.Error_IllScopedTerm, uu____10200) in
          FStar_Errors.raise_error uu____10195 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____10226 =
            let uu____10231 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
            FStar_Util.Inl uu____10231 in
          value_check_expected_typ env1 e uu____10226
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____10233 =
            let uu____10246 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____10246 with
            | FStar_Pervasives_Native.None ->
                let uu____10261 = FStar_Syntax_Util.type_u () in
                (match uu____10261 with
                 | (k, u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard) in
          (match uu____10233 with
           | (t, uu____10298, g0) ->
               let uu____10312 =
                 let uu____10325 =
                   let uu____10326 = FStar_Range.string_of_range r in
                   Prims.op_Hat "user-provided implicit term at " uu____10326 in
                 FStar_TypeChecker_Util.new_implicit_var uu____10325 r env1 t in
               (match uu____10312 with
                | (e1, uu____10334, g1) ->
                    let uu____10348 =
                      let uu____10349 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____10349
                        FStar_TypeChecker_Common.lcomp_of_comp in
                    let uu____10350 = FStar_TypeChecker_Env.conj_guard g0 g1 in
                    (e1, uu____10348, uu____10350)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10352 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10361 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____10361)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____10352 with
           | (t, rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1418_10374 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1418_10374.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1418_10374.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____10377 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____10377 with
                 | (e2, t1, implicits) ->
                     let tc =
                       let uu____10398 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____10398
                       then FStar_Util.Inl t1
                       else
                         (let uu____10404 =
                            let uu____10405 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____10405 in
                          FStar_Util.Inr uu____10404) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10407;
             FStar_Syntax_Syntax.vars = uu____10408;_},
           uu____10409)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10414 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10414
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10422 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10422
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10430;
             FStar_Syntax_Syntax.vars = uu____10431;_},
           us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____10440 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10440 with
           | ((us', t), range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range in
               (maybe_warn_on_use env1 fv1;
                if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10465 =
                     let uu____10470 =
                       let uu____10471 = FStar_Syntax_Print.fv_to_string fv1 in
                       let uu____10472 =
                         FStar_Util.string_of_int (FStar_List.length us1) in
                       let uu____10473 =
                         FStar_Util.string_of_int (FStar_List.length us') in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10471 uu____10472 uu____10473 in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10470) in
                   let uu____10474 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____10465 uu____10474)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10492 -> failwith "Impossible") us' us1;
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____10495 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____10495 us1 in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_uinst (uu____10496, us) ->
          let uu____10502 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
              "Universe applications are only allowed on top-level identifiers")
            uu____10502
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10510 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10510 with
           | ((us, t), range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range in
               (maybe_warn_on_use env1 fv1;
                (let uu____10535 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____10535
                 then
                   let uu____10536 =
                     let uu____10537 = FStar_Syntax_Syntax.lid_of_fv fv1 in
                     FStar_Syntax_Print.lid_to_string uu____10537 in
                   let uu____10538 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____10539 = FStar_Range.string_of_range range in
                   let uu____10540 = FStar_Range.string_of_use_range range in
                   let uu____10541 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____10536 uu____10538 uu____10539 uu____10540
                     uu____10541
                 else ());
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____10545 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____10545 us in
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
          let uu____10573 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10573 with
           | (bs1, c1) ->
               let env0 = env1 in
               let uu____10587 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____10587 with
                | (env2, uu____10601) ->
                    let uu____10606 = tc_binders env2 bs1 in
                    (match uu____10606 with
                     | (bs2, env3, g, us) ->
                         let uu____10625 = tc_comp env3 c1 in
                         (match uu____10625 with
                          | (c2, uc, f) ->
                              let e1 =
                                let uu___1504_10644 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1504_10644.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1504_10644.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____10655 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____10655 in
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
          let uu____10671 =
            let uu____10676 =
              let uu____10677 = FStar_Syntax_Syntax.mk_binder x in
              [uu____10677] in
            FStar_Syntax_Subst.open_term uu____10676 phi in
          (match uu____10671 with
           | (x1, phi1) ->
               let env0 = env1 in
               let uu____10705 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____10705 with
                | (env2, uu____10719) ->
                    let uu____10724 =
                      let uu____10739 = FStar_List.hd x1 in
                      tc_binder env2 uu____10739 in
                    (match uu____10724 with
                     | (x2, env3, f1, u) ->
                         ((let uu____10775 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____10775
                           then
                             let uu____10776 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____10777 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____10778 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10776 uu____10777 uu____10778
                           else ());
                          (let uu____10782 = FStar_Syntax_Util.type_u () in
                           match uu____10782 with
                           | (t_phi, uu____10794) ->
                               let uu____10795 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                   "refinement formula must be pure or ghost" in
                               (match uu____10795 with
                                | (phi2, uu____10809, f2) ->
                                    let e1 =
                                      let uu___1542_10814 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1542_10814.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1542_10814.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____10823 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10823 in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____10851) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____10878 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
            if uu____10878
            then
              let uu____10879 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1555_10882 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1555_10882.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1555_10882.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10879
            else ());
           (let uu____10896 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____10896 with
            | (bs2, body1) -> tc_abs env1 top bs2 body1))
      | uu____10909 ->
          let uu____10910 =
            let uu____10911 = FStar_Syntax_Print.term_to_string top in
            let uu____10912 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10911
              uu____10912 in
          failwith uu____10910
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
          | FStar_Const.Const_bool uu____10923 -> FStar_Syntax_Util.t_bool
          | FStar_Const.Const_int (uu____10924, FStar_Pervasives_Native.None)
              -> FStar_Syntax_Syntax.t_int
          | FStar_Const.Const_int
              (uu____10935, FStar_Pervasives_Native.Some msize) ->
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
          | FStar_Const.Const_string uu____10951 ->
              FStar_Syntax_Syntax.t_string
          | FStar_Const.Const_real uu____10956 -> FStar_Syntax_Syntax.t_real
          | FStar_Const.Const_float uu____10957 ->
              FStar_Syntax_Syntax.t_float
          | FStar_Const.Const_char uu____10958 ->
              let uu____10959 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
              FStar_All.pipe_right uu____10959 FStar_Util.must
          | FStar_Const.Const_effect -> FStar_Syntax_Util.ktype0
          | FStar_Const.Const_range uu____10964 ->
              FStar_Syntax_Syntax.t_range
          | FStar_Const.Const_range_of ->
              let uu____10965 =
                let uu____10970 =
                  let uu____10971 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____10971 in
                (FStar_Errors.Fatal_IllTyped, uu____10970) in
              FStar_Errors.raise_error uu____10965 r
          | FStar_Const.Const_set_range_of ->
              let uu____10972 =
                let uu____10977 =
                  let uu____10978 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____10978 in
                (FStar_Errors.Fatal_IllTyped, uu____10977) in
              FStar_Errors.raise_error uu____10972 r
          | FStar_Const.Const_reify ->
              let uu____10979 =
                let uu____10984 =
                  let uu____10985 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____10985 in
                (FStar_Errors.Fatal_IllTyped, uu____10984) in
              FStar_Errors.raise_error uu____10979 r
          | FStar_Const.Const_reflect uu____10986 ->
              let uu____10987 =
                let uu____10992 =
                  let uu____10993 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____10993 in
                (FStar_Errors.Fatal_IllTyped, uu____10992) in
              FStar_Errors.raise_error uu____10987 r
          | uu____10994 ->
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
      | FStar_Syntax_Syntax.Total (t, uu____11011) ->
          let uu____11020 = FStar_Syntax_Util.type_u () in
          (match uu____11020 with
           | (k, u) ->
               let uu____11033 = tc_check_tot_or_gtot_term env t k "" in
               (match uu____11033 with
                | (t1, uu____11047, g) ->
                    let uu____11049 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____11049, u, g)))
      | FStar_Syntax_Syntax.GTotal (t, uu____11051) ->
          let uu____11060 = FStar_Syntax_Util.type_u () in
          (match uu____11060 with
           | (k, u) ->
               let uu____11073 = tc_check_tot_or_gtot_term env t k "" in
               (match uu____11073 with
                | (t1, uu____11087, g) ->
                    let uu____11089 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____11089, u, g)))
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
            let uu____11097 =
              let uu____11098 =
                FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ in
              uu____11098 :: (c1.FStar_Syntax_Syntax.effect_args) in
            FStar_Syntax_Syntax.mk_Tm_app head1 uu____11097
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____11115 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff "" in
          (match uu____11115 with
           | (tc1, uu____11129, f) ->
               let uu____11131 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____11131 with
                | (head2, args) ->
                    let comp_univs =
                      let uu____11181 =
                        let uu____11182 = FStar_Syntax_Subst.compress head2 in
                        uu____11182.FStar_Syntax_Syntax.n in
                      match uu____11181 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11185, us) -> us
                      | uu____11191 -> [] in
                    let uu____11192 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____11192 with
                     | (uu____11215, args1) ->
                         let uu____11241 =
                           let uu____11264 = FStar_List.hd args1 in
                           let uu____11281 = FStar_List.tl args1 in
                           (uu____11264, uu____11281) in
                         (match uu____11241 with
                          | (res, args2) ->
                              let uu____11362 =
                                let uu____11371 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_11399 ->
                                          match uu___5_11399 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____11407 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____11407 with
                                               | (env1, uu____11419) ->
                                                   let uu____11424 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____11424 with
                                                    | (e1, uu____11436, g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard))) in
                                FStar_All.pipe_right uu____11371
                                  FStar_List.unzip in
                              (match uu____11362 with
                               | (flags, guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1685_11477 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1685_11477.FStar_Syntax_Syntax.effect_name);
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
                                   let uu____11483 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards in
                                   (c2, u_c, uu____11483))))))
and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____11493 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____11494 -> u2
        | FStar_Syntax_Syntax.U_zero -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____11506 = aux u3 in
            FStar_Syntax_Syntax.U_succ uu____11506
        | FStar_Syntax_Syntax.U_max us ->
            let uu____11510 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____11510
        | FStar_Syntax_Syntax.U_name x ->
            let uu____11514 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x) in
            if uu____11514
            then u2
            else
              (let uu____11516 =
                 let uu____11517 =
                   let uu____11518 = FStar_Syntax_Print.univ_to_string u2 in
                   Prims.op_Hat uu____11518 " not found" in
                 Prims.op_Hat "Universe variable " uu____11517 in
               failwith uu____11516) in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown ->
             let uu____11520 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____11520 FStar_Pervasives_Native.snd
         | uu____11529 -> aux u)
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
                | uu____11563 ->
                    failwith
                      "Impossible: Can't have a let rec annotation but no expected type");
               (let uu____11574 = tc_binders env bs in
                match uu____11574 with
                | (bs1, envbody, g_env, uu____11604) ->
                    (FStar_Pervasives_Native.None, bs1, [],
                      FStar_Pervasives_Native.None, envbody, body, g_env)))
          | FStar_Pervasives_Native.Some t ->
              let t1 = FStar_Syntax_Subst.compress t in
              let rec as_function_typ norm1 t2 =
                let uu____11648 =
                  let uu____11649 = FStar_Syntax_Subst.compress t2 in
                  uu____11649.FStar_Syntax_Syntax.n in
                match uu____11648 with
                | FStar_Syntax_Syntax.Tm_uvar uu____11672 ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____11694 -> failwith "Impossible");
                     (let uu____11705 = tc_binders env bs in
                      match uu____11705 with
                      | (bs1, envbody, g_env, uu____11737) ->
                          let uu____11738 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody in
                          (match uu____11738 with
                           | (envbody1, uu____11766) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____11777;
                       FStar_Syntax_Syntax.pos = uu____11778;
                       FStar_Syntax_Syntax.vars = uu____11779;_},
                     uu____11780)
                    ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____11826 -> failwith "Impossible");
                     (let uu____11837 = tc_binders env bs in
                      match uu____11837 with
                      | (bs1, envbody, g_env, uu____11869) ->
                          let uu____11870 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody in
                          (match uu____11870 with
                           | (envbody1, uu____11898) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_refine (b, uu____11910) ->
                    let uu____11915 =
                      as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                    (match uu____11915 with
                     | (uu____11956, bs1, bs', copt, env_body, body1, g_env)
                         ->
                         ((FStar_Pervasives_Native.Some t2), bs1, bs', copt,
                           env_body, body1, g_env))
                | FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) ->
                    let uu____12003 =
                      FStar_Syntax_Subst.open_comp bs_expected c_expected in
                    (match uu____12003 with
                     | (bs_expected1, c_expected1) ->
                         let check_actuals_against_formals env1 bs1
                           bs_expected2 body1 =
                           let rec handle_more uu____12138 c_expected2 body2
                             =
                             match uu____12138 with
                             | (env_bs, bs2, more, guard_env, subst) ->
                                 (match more with
                                  | FStar_Pervasives_Native.None ->
                                      let uu____12252 =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2 in
                                      (env_bs, bs2, guard_env, uu____12252,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inr more_bs_expected) ->
                                      let c =
                                        let uu____12269 =
                                          FStar_Syntax_Util.arrow
                                            more_bs_expected c_expected2 in
                                        FStar_Syntax_Syntax.mk_Total
                                          uu____12269 in
                                      let uu____12270 =
                                        FStar_Syntax_Subst.subst_comp subst c in
                                      (env_bs, bs2, guard_env, uu____12270,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inl more_bs) ->
                                      let c =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2 in
                                      let uu____12287 =
                                        (FStar_Options.ml_ish ()) ||
                                          (FStar_Syntax_Util.is_named_tot c) in
                                      if uu____12287
                                      then
                                        let t3 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env_bs
                                            (FStar_Syntax_Util.comp_result c) in
                                        (match t3.FStar_Syntax_Syntax.n with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs_expected3, c_expected3) ->
                                             let uu____12351 =
                                               FStar_Syntax_Subst.open_comp
                                                 bs_expected3 c_expected3 in
                                             (match uu____12351 with
                                              | (bs_expected4, c_expected4)
                                                  ->
                                                  let uu____12378 =
                                                    tc_abs_check_binders
                                                      env_bs more_bs
                                                      bs_expected4 in
                                                  (match uu____12378 with
                                                   | (env_bs_bs', bs', more1,
                                                      guard'_env_bs, subst1)
                                                       ->
                                                       let guard'_env =
                                                         FStar_TypeChecker_Env.close_guard
                                                           env_bs bs2
                                                           guard'_env_bs in
                                                       let uu____12433 =
                                                         let uu____12460 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard_env
                                                             guard'_env in
                                                         (env_bs_bs',
                                                           (FStar_List.append
                                                              bs2 bs'),
                                                           more1,
                                                           uu____12460,
                                                           subst1) in
                                                       handle_more
                                                         uu____12433
                                                         c_expected4 body2))
                                         | uu____12483 ->
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
                           let uu____12511 =
                             tc_abs_check_binders env1 bs1 bs_expected2 in
                           handle_more uu____12511 c_expected1 body1 in
                         let mk_letrec_env envbody bs1 c =
                           let letrecs = guard_letrecs envbody bs1 c in
                           let envbody1 =
                             let uu___1816_12576 = envbody in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1816_12576.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1816_12576.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1816_12576.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1816_12576.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1816_12576.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1816_12576.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1816_12576.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1816_12576.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1816_12576.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1816_12576.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1816_12576.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1816_12576.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1816_12576.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs = [];
                               FStar_TypeChecker_Env.top_level =
                                 (uu___1816_12576.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1816_12576.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___1816_12576.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (uu___1816_12576.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1816_12576.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1816_12576.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1816_12576.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1816_12576.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1816_12576.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1816_12576.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1816_12576.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1816_12576.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1816_12576.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1816_12576.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1816_12576.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1816_12576.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1816_12576.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1816_12576.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1816_12576.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1816_12576.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1816_12576.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1816_12576.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1816_12576.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1816_12576.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1816_12576.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1816_12576.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1816_12576.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1816_12576.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1816_12576.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1816_12576.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1816_12576.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1816_12576.FStar_TypeChecker_Env.erasable_types_tab);
                               FStar_TypeChecker_Env.enable_defer_to_tac =
                                 (uu___1816_12576.FStar_TypeChecker_Env.enable_defer_to_tac)
                             } in
                           let uu____12585 =
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____12651 ->
                                     fun uu____12652 ->
                                       match (uu____12651, uu____12652) with
                                       | ((env1, letrec_binders, g),
                                          (l, t3, u_names)) ->
                                           let uu____12743 =
                                             let uu____12750 =
                                               let uu____12751 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env1 in
                                               FStar_All.pipe_right
                                                 uu____12751
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____12750 t3 in
                                           (match uu____12743 with
                                            | (t4, uu____12775, g') ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env1 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____12788 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___1834_12791
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___1834_12791.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___1834_12791.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____12788 ::
                                                        letrec_binders
                                                  | uu____12792 ->
                                                      letrec_binders in
                                                let uu____12797 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g' in
                                                (env2, lb, uu____12797)))
                                  (envbody1, [],
                                    FStar_TypeChecker_Env.trivial_guard)) in
                           match uu____12585 with
                           | (envbody2, letrec_binders, g) ->
                               let uu____12817 =
                                 FStar_TypeChecker_Env.close_guard envbody2
                                   bs1 g in
                               (envbody2, letrec_binders, uu____12817) in
                         let envbody =
                           let uu___1842_12821 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1842_12821.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1842_12821.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1842_12821.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1842_12821.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1842_12821.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1842_12821.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1842_12821.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1842_12821.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1842_12821.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1842_12821.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1842_12821.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1842_12821.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1842_12821.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs = [];
                             FStar_TypeChecker_Env.top_level =
                               (uu___1842_12821.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1842_12821.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1842_12821.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1842_12821.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1842_12821.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1842_12821.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___1842_12821.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1842_12821.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1842_12821.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1842_12821.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1842_12821.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1842_12821.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1842_12821.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1842_12821.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1842_12821.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1842_12821.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1842_12821.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1842_12821.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1842_12821.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1842_12821.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1842_12821.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1842_12821.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1842_12821.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1842_12821.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1842_12821.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1842_12821.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1842_12821.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1842_12821.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1842_12821.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1842_12821.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1842_12821.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1842_12821.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1842_12821.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let uu____12830 =
                           check_actuals_against_formals envbody bs
                             bs_expected1 body in
                         (match uu____12830 with
                          | (envbody1, bs1, g_env, c, body1) ->
                              let envbody2 =
                                let uu___1851_12867 = envbody1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1851_12867.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1851_12867.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1851_12867.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___1851_12867.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1851_12867.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___1851_12867.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1851_12867.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1851_12867.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1851_12867.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1851_12867.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1851_12867.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1851_12867.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1851_12867.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (env.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1851_12867.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1851_12867.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1851_12867.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1851_12867.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1851_12867.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1851_12867.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1851_12867.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1851_12867.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1851_12867.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1851_12867.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1851_12867.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1851_12867.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1851_12867.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1851_12867.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1851_12867.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1851_12867.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1851_12867.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1851_12867.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1851_12867.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1851_12867.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1851_12867.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1851_12867.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1851_12867.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1851_12867.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1851_12867.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1851_12867.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1851_12867.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1851_12867.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1851_12867.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1851_12867.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1851_12867.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1851_12867.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1851_12867.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____12868 = mk_letrec_env envbody2 bs1 c in
                              (match uu____12868 with
                               | (envbody3, letrecs, g_annots) ->
                                   let envbody4 =
                                     FStar_TypeChecker_Env.set_expected_typ
                                       envbody3
                                       (FStar_Syntax_Util.comp_result c) in
                                   let uu____12905 =
                                     FStar_TypeChecker_Env.conj_guard g_env
                                       g_annots in
                                   ((FStar_Pervasives_Native.Some t2), bs1,
                                     letrecs,
                                     (FStar_Pervasives_Native.Some c),
                                     envbody4, body1, uu____12905))))
                | uu____12912 ->
                    if Prims.op_Negation norm1
                    then
                      let uu____12933 =
                        let uu____12934 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.unfold_whnf env) in
                        FStar_All.pipe_right uu____12934
                          FStar_Syntax_Util.unascribe in
                      as_function_typ true uu____12933
                    else
                      (let uu____12936 =
                         tc_abs_expected_function_typ env bs
                           FStar_Pervasives_Native.None body in
                       match uu____12936 with
                       | (uu____12975, bs1, uu____12977, c_opt, envbody,
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
        let rec aux uu____13050 bs1 bs_expected1 =
          match uu____13050 with
          | (env1, subst) ->
              (match (bs1, bs_expected1) with
               | ([], []) ->
                   (env1, [], FStar_Pervasives_Native.None,
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ((uu____13157, FStar_Pervasives_Native.None)::uu____13158,
                  (hd_e, q)::uu____13161) when
                   FStar_Syntax_Syntax.is_implicit_or_meta q ->
                   let bv =
                     let uu____13213 =
                       let uu____13216 =
                         FStar_Ident.range_of_id
                           hd_e.FStar_Syntax_Syntax.ppname in
                       FStar_Pervasives_Native.Some uu____13216 in
                     let uu____13217 =
                       FStar_Syntax_Subst.subst subst
                         hd_e.FStar_Syntax_Syntax.sort in
                     FStar_Syntax_Syntax.new_bv uu____13213 uu____13217 in
                   aux (env1, subst) ((bv, q) :: bs1) bs_expected1
               | ((hd, imp)::bs2, (hd_expected, imp')::bs_expected2) ->
                   ((let special q1 q2 =
                       match (q1, q2) with
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13310),
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13311)) -> true
                       | (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Equality)) -> true
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____13320),
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13321)) -> true
                       | uu____13326 -> false in
                     let uu____13335 =
                       (Prims.op_Negation (special imp imp')) &&
                         (let uu____13337 =
                            FStar_Syntax_Util.eq_aqual imp imp' in
                          uu____13337 <> FStar_Syntax_Util.Equal) in
                     if uu____13335
                     then
                       let uu____13338 =
                         let uu____13343 =
                           let uu____13344 =
                             FStar_Syntax_Print.bv_to_string hd in
                           FStar_Util.format1
                             "Inconsistent implicit argument annotation on argument %s"
                             uu____13344 in
                         (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                           uu____13343) in
                       let uu____13345 = FStar_Syntax_Syntax.range_of_bv hd in
                       FStar_Errors.raise_error uu____13338 uu____13345
                     else ());
                    (let expected_t =
                       FStar_Syntax_Subst.subst subst
                         hd_expected.FStar_Syntax_Syntax.sort in
                     let uu____13348 =
                       let uu____13355 =
                         let uu____13356 =
                           FStar_Syntax_Util.unmeta
                             hd.FStar_Syntax_Syntax.sort in
                         uu____13356.FStar_Syntax_Syntax.n in
                       match uu____13355 with
                       | FStar_Syntax_Syntax.Tm_unknown ->
                           (expected_t, FStar_TypeChecker_Env.trivial_guard)
                       | uu____13367 ->
                           ((let uu____13369 =
                               FStar_TypeChecker_Env.debug env1
                                 FStar_Options.High in
                             if uu____13369
                             then
                               let uu____13370 =
                                 FStar_Syntax_Print.bv_to_string hd in
                               FStar_Util.print1 "Checking binder %s\n"
                                 uu____13370
                             else ());
                            (let uu____13372 =
                               tc_tot_or_gtot_term env1
                                 hd.FStar_Syntax_Syntax.sort in
                             match uu____13372 with
                             | (t, uu____13386, g1_env) ->
                                 let g2_env =
                                   let uu____13389 =
                                     FStar_TypeChecker_Rel.teq_nosmt env1 t
                                       expected_t in
                                   match uu____13389 with
                                   | FStar_Pervasives_Native.Some g ->
                                       FStar_All.pipe_right g
                                         (FStar_TypeChecker_Rel.resolve_implicits
                                            env1)
                                   | FStar_Pervasives_Native.None ->
                                       let uu____13393 =
                                         FStar_TypeChecker_Rel.get_subtyping_prop
                                           env1 expected_t t in
                                       (match uu____13393 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu____13396 =
                                              FStar_TypeChecker_Err.basic_type_error
                                                env1
                                                FStar_Pervasives_Native.None
                                                expected_t t in
                                            let uu____13401 =
                                              FStar_TypeChecker_Env.get_range
                                                env1 in
                                            FStar_Errors.raise_error
                                              uu____13396 uu____13401
                                        | FStar_Pervasives_Native.Some g_env
                                            ->
                                            FStar_TypeChecker_Util.label_guard
                                              (hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                              "Type annotation on parameter incompatible with the expected type"
                                              g_env) in
                                 let uu____13403 =
                                   FStar_TypeChecker_Env.conj_guard g1_env
                                     g2_env in
                                 (t, uu____13403))) in
                     match uu____13348 with
                     | (t, g_env) ->
                         let hd1 =
                           let uu___1947_13429 = hd in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1947_13429.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1947_13429.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t
                           } in
                         let b = (hd1, imp) in
                         let b_expected = (hd_expected, imp') in
                         let env_b = push_binding env1 b in
                         let subst1 =
                           let uu____13452 =
                             FStar_Syntax_Syntax.bv_to_name hd1 in
                           maybe_extend_subst subst b_expected uu____13452 in
                         let uu____13455 =
                           aux (env_b, subst1) bs2 bs_expected2 in
                         (match uu____13455 with
                          | (env_bs, bs3, rest, g'_env_b, subst2) ->
                              let g'_env =
                                FStar_TypeChecker_Env.close_guard env_bs 
                                  [b] g'_env_b in
                              let uu____13520 =
                                FStar_TypeChecker_Env.conj_guard g_env g'_env in
                              (env_bs, (b :: bs3), rest, uu____13520, subst2))))
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
            let uu____13657 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top in
            FStar_Errors.raise_error uu____13657 top.FStar_Syntax_Syntax.pos in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____13663 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____13663 with
          | (env1, topt) ->
              ((let uu____13683 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____13683
                then
                  let uu____13684 =
                    match topt with
                    | FStar_Pervasives_Native.None -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13684
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13688 =
                  tc_abs_expected_function_typ env1 bs topt body in
                match uu____13688 with
                | (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1,
                   g_env) ->
                    ((let uu____13729 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme in
                      if uu____13729
                      then
                        let uu____13730 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t in
                        let uu____13732 =
                          match c_opt with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t in
                        let uu____13734 =
                          let uu____13735 =
                            FStar_TypeChecker_Env.expected_typ envbody in
                          match uu____13735 with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____13730 uu____13732 uu____13734
                      else ());
                     (let uu____13741 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC") in
                      if uu____13741
                      then
                        let uu____13742 =
                          FStar_Syntax_Print.binders_to_string ", " bs1 in
                        let uu____13743 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13742 uu____13743
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos in
                      let uu____13746 =
                        let uu____13757 =
                          let uu____13764 =
                            (FStar_All.pipe_right c_opt FStar_Util.is_some)
                              &&
                              (let uu____13772 =
                                 let uu____13773 =
                                   FStar_Syntax_Subst.compress body1 in
                                 uu____13773.FStar_Syntax_Syntax.n in
                               match uu____13772 with
                               | FStar_Syntax_Syntax.Tm_app (head, args) when
                                   (FStar_List.length args) = Prims.int_one
                                   ->
                                   let uu____13810 =
                                     let uu____13811 =
                                       FStar_Syntax_Subst.compress head in
                                     uu____13811.FStar_Syntax_Syntax.n in
                                   (match uu____13810 with
                                    | FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reflect
                                        uu____13814) -> true
                                    | uu____13815 -> false)
                               | uu____13816 -> false) in
                          if uu____13764
                          then
                            let uu____13823 =
                              let uu____13824 =
                                FStar_TypeChecker_Env.clear_expected_typ
                                  envbody1 in
                              FStar_All.pipe_right uu____13824
                                FStar_Pervasives_Native.fst in
                            let uu____13839 =
                              let uu____13840 =
                                let uu____13841 =
                                  let uu____13868 =
                                    let uu____13885 =
                                      let uu____13894 =
                                        FStar_All.pipe_right c_opt
                                          FStar_Util.must in
                                      FStar_Util.Inr uu____13894 in
                                    (uu____13885,
                                      FStar_Pervasives_Native.None) in
                                  (body1, uu____13868,
                                    FStar_Pervasives_Native.None) in
                                FStar_Syntax_Syntax.Tm_ascribed uu____13841 in
                              FStar_Syntax_Syntax.mk uu____13840
                                FStar_Range.dummyRange in
                            (uu____13823, uu____13839, false)
                          else
                            (let uu____13940 =
                               let uu____13941 =
                                 let uu____13948 =
                                   let uu____13949 =
                                     FStar_Syntax_Subst.compress body1 in
                                   uu____13949.FStar_Syntax_Syntax.n in
                                 (c_opt, uu____13948) in
                               match uu____13941 with
                               | (FStar_Pervasives_Native.None,
                                  FStar_Syntax_Syntax.Tm_ascribed
                                  (uu____13954,
                                   (FStar_Util.Inr expected_c, uu____13956),
                                   uu____13957)) -> false
                               | uu____14006 -> true in
                             (envbody1, body1, uu____13940)) in
                        match uu____13757 with
                        | (envbody2, body2, should_check_expected_effect) ->
                            let uu____14026 =
                              tc_term
                                (let uu___2032_14035 = envbody2 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2032_14035.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2032_14035.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2032_14035.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2032_14035.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2032_14035.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2032_14035.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2032_14035.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2032_14035.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2032_14035.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2032_14035.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2032_14035.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2032_14035.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2032_14035.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2032_14035.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level = false;
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2032_14035.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___2032_14035.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2032_14035.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2032_14035.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___2032_14035.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2032_14035.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2032_14035.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2032_14035.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2032_14035.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2032_14035.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2032_14035.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2032_14035.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2032_14035.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2032_14035.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2032_14035.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2032_14035.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2032_14035.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2032_14035.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2032_14035.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2032_14035.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___2032_14035.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2032_14035.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___2032_14035.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2032_14035.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2032_14035.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2032_14035.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2032_14035.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2032_14035.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___2032_14035.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___2032_14035.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___2032_14035.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) body2 in
                            (match uu____14026 with
                             | (body3, cbody, guard_body) ->
                                 let guard_body1 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     envbody2 guard_body in
                                 if should_check_expected_effect
                                 then
                                   let uu____14060 =
                                     FStar_TypeChecker_Common.lcomp_comp
                                       cbody in
                                   (match uu____14060 with
                                    | (cbody1, g_lc) ->
                                        let uu____14077 =
                                          check_expected_effect
                                            (let uu___2043_14086 = envbody2 in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 use_eq;
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.lax);
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.phase1);
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___2043_14086.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) c_opt (body3, cbody1) in
                                        (match uu____14077 with
                                         | (body4, cbody2, guard) ->
                                             let uu____14100 =
                                               let uu____14101 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_lc guard in
                                               FStar_TypeChecker_Env.conj_guard
                                                 guard_body1 uu____14101 in
                                             (body4, cbody2, uu____14100)))
                                 else
                                   (let uu____14107 =
                                      FStar_TypeChecker_Common.lcomp_comp
                                        cbody in
                                    match uu____14107 with
                                    | (cbody1, g_lc) ->
                                        let uu____14124 =
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 g_lc in
                                        (body3, cbody1, uu____14124))) in
                      match uu____13746 with
                      | (body2, cbody, guard_body) ->
                          let guard =
                            let uu____14147 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14149 =
                                   FStar_TypeChecker_Env.should_verify env1 in
                                 Prims.op_Negation uu____14149) in
                            if uu____14147
                            then
                              let uu____14150 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env in
                              let uu____14151 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body in
                              FStar_TypeChecker_Env.conj_guard uu____14150
                                uu____14151
                            else
                              (let guard =
                                 let uu____14154 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14154 in
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
                          let uu____14168 =
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
                                 | FStar_Syntax_Syntax.Tm_arrow uu____14191
                                     -> (e, t_annot, guard1)
                                 | uu____14206 ->
                                     let lc =
                                       let uu____14208 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed in
                                       FStar_All.pipe_right uu____14208
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     let uu____14209 =
                                       FStar_TypeChecker_Util.check_has_type
                                         env1 e lc t1 in
                                     (match uu____14209 with
                                      | (e1, uu____14223, guard') ->
                                          let uu____14225 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard' in
                                          (e1, t_annot, uu____14225)))
                            | FStar_Pervasives_Native.None ->
                                (e, tfun_computed, guard1) in
                          (match uu____14168 with
                           | (e1, tfun, guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun in
                               let uu____14236 =
                                 let uu____14241 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____14241 guard2 in
                               (match uu____14236 with
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
              (let uu____14291 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____14291
               then
                 let uu____14292 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos in
                 let uu____14293 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14292
                   uu____14293
               else ());
              (let monadic_application uu____14372 subst arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____14372 with
                 | (head1, chead1, ghead1, cres) ->
                     let uu____14441 =
                       check_no_escape (FStar_Pervasives_Native.Some head1)
                         env fvs (FStar_Syntax_Util.comp_result cres) in
                     (match uu____14441 with
                      | (rt, g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt in
                          let uu____14455 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____14471 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____14471 in
                                (cres1, g)
                            | uu____14472 ->
                                let g =
                                  let uu____14482 =
                                    let uu____14483 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard in
                                    FStar_All.pipe_right uu____14483
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env) in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____14482 in
                                let uu____14484 =
                                  let uu____14485 =
                                    FStar_Syntax_Util.arrow bs cres1 in
                                  FStar_Syntax_Syntax.mk_Total uu____14485 in
                                (uu____14484, g) in
                          (match uu____14455 with
                           | (cres2, guard1) ->
                               ((let uu____14495 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium in
                                 if uu____14495
                                 then
                                   let uu____14496 =
                                     FStar_Syntax_Print.comp_to_string cres2 in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____14496
                                 else ());
                                (let uu____14498 =
                                   let uu____14503 =
                                     let uu____14504 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         chead1 in
                                     FStar_All.pipe_right uu____14504
                                       FStar_TypeChecker_Common.lcomp_of_comp in
                                   let uu____14505 =
                                     let uu____14506 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         cres2 in
                                     FStar_All.pipe_right uu____14506
                                       FStar_TypeChecker_Common.lcomp_of_comp in
                                   (uu____14503, uu____14505) in
                                 match uu____14498 with
                                 | (chead2, cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____14529 ->
                                                 match uu____14529 with
                                                 | (uu____14538, uu____14539,
                                                    lc) ->
                                                     (let uu____14547 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc in
                                                      Prims.op_Negation
                                                        uu____14547)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev) in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head1
                                           (FStar_List.rev arg_rets_rev)
                                           head1.FStar_Syntax_Syntax.pos in
                                       let uu____14557 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful in
                                       if uu____14557
                                       then
                                         ((let uu____14559 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____14559
                                           then
                                             let uu____14560 =
                                               FStar_Syntax_Print.term_to_string
                                                 term in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____14560
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____14564 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____14564
                                           then
                                             let uu____14565 =
                                               FStar_Syntax_Print.term_to_string
                                                 term in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____14565
                                           else ());
                                          cres3) in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c ->
                                            fun uu____14593 ->
                                              match uu____14593 with
                                              | ((e, q), x, c) ->
                                                  ((let uu____14635 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14635
                                                    then
                                                      let uu____14636 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                            -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1 in
                                                      let uu____14638 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e in
                                                      let uu____14639 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____14636
                                                        uu____14638
                                                        uu____14639
                                                    else ());
                                                   (let uu____14641 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c in
                                                    if uu____14641
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
                                       (let uu____14649 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme in
                                        if uu____14649
                                        then
                                          let uu____14650 =
                                            FStar_Syntax_Print.term_to_string
                                              head1 in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____14650
                                        else ());
                                       (let uu____14652 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2 in
                                        if uu____14652
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
                                       let uu____14659 =
                                         let uu____14660 =
                                           FStar_Syntax_Subst.compress head1 in
                                         uu____14660.FStar_Syntax_Syntax.n in
                                       match uu____14659 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____14664 -> false in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1 ->
                                                fun uu____14685 ->
                                                  match uu____14685 with
                                                  | (arg, uu____14699,
                                                     uu____14700) -> arg ::
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
                                         (let uu____14708 =
                                            let map_fun uu____14774 =
                                              match uu____14774 with
                                              | ((e, q), uu____14815, c) ->
                                                  ((let uu____14838 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14838
                                                    then
                                                      let uu____14839 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e in
                                                      let uu____14840 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____14839
                                                        uu____14840
                                                    else ());
                                                   (let uu____14842 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c in
                                                    if uu____14842
                                                    then
                                                      ((let uu____14866 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme in
                                                        if uu____14866
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
                                                           (let uu____14901 =
                                                              let uu____14902
                                                                =
                                                                let uu____14903
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head1 in
                                                                uu____14903.FStar_Syntax_Syntax.n in
                                                              match uu____14902
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____14907
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore" in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____14907
                                                              | uu____14908
                                                                  -> true in
                                                            Prims.op_Negation
                                                              uu____14901) in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____14910 =
                                                            let uu____14915 =
                                                              let uu____14916
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e in
                                                              let uu____14917
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  c.FStar_TypeChecker_Common.eff_name in
                                                              let uu____14918
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____14916
                                                                uu____14917
                                                                uu____14918 in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____14915) in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____14910)
                                                       else ();
                                                       (let uu____14921 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme in
                                                        if uu____14921
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
                                                        let uu____14925 =
                                                          let uu____14934 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          (uu____14934, q) in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____14925))))) in
                                            let uu____14963 =
                                              let uu____14994 =
                                                let uu____15023 =
                                                  let uu____15034 =
                                                    let uu____15043 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head1 in
                                                    (uu____15043,
                                                      FStar_Pervasives_Native.None,
                                                      chead2) in
                                                  uu____15034 ::
                                                    arg_comps_rev in
                                                FStar_List.map map_fun
                                                  uu____15023 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____14994 in
                                            match uu____14963 with
                                            | (lifted_args, reverse_args) ->
                                                let uu____15244 =
                                                  let uu____15245 =
                                                    FStar_List.hd
                                                      reverse_args in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15245 in
                                                let uu____15266 =
                                                  let uu____15267 =
                                                    FStar_List.tl
                                                      reverse_args in
                                                  FStar_List.rev uu____15267 in
                                                (lifted_args, uu____15244,
                                                  uu____15266) in
                                          match uu____14708 with
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
                                                uu___6_15376 =
                                                match uu___6_15376 with
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
                                                      let uu____15437 =
                                                        let uu____15438 =
                                                          let uu____15451 =
                                                            let uu____15454 =
                                                              let uu____15455
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x in
                                                              [uu____15455] in
                                                            FStar_Syntax_Subst.close
                                                              uu____15454 e in
                                                          ((false, [lb]),
                                                            uu____15451) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____15438 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____15437
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
                                     let uu____15504 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1 in
                                     (match uu____15504 with
                                      | (comp2, g) ->
                                          ((let uu____15521 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme in
                                            if uu____15521
                                            then
                                              let uu____15522 =
                                                FStar_Syntax_Print.term_to_string
                                                  app in
                                              let uu____15523 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____15522 uu____15523
                                            else ());
                                           (app, comp2, g))))))) in
               let rec tc_args head_info uu____15609 bs args1 =
                 match uu____15609 with
                 | (subst, outargs, arg_rets, g, fvs) ->
                     (match (bs, args1) with
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15772))::rest,
                         (uu____15774, FStar_Pervasives_Native.None)::uu____15775)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort in
                          let uu____15835 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head) env fvs t in
                          (match uu____15835 with
                           | (t1, g_ex) ->
                               let r1 =
                                 match outargs with
                                 | [] -> head.FStar_Syntax_Syntax.pos
                                 | ((t2, uu____15866), uu____15867,
                                    uu____15868)::uu____15869 ->
                                     let uu____15924 =
                                       FStar_Range.def_range
                                         head.FStar_Syntax_Syntax.pos in
                                     let uu____15925 =
                                       let uu____15926 =
                                         FStar_Range.use_range
                                           head.FStar_Syntax_Syntax.pos in
                                       let uu____15927 =
                                         FStar_Range.use_range
                                           t2.FStar_Syntax_Syntax.pos in
                                       FStar_Range.union_rng uu____15926
                                         uu____15927 in
                                     FStar_Range.range_of_rng uu____15924
                                       uu____15925 in
                               let uu____15928 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   r1 env t1 in
                               (match uu____15928 with
                                | (varg, uu____15948, implicits) ->
                                    let subst1 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst in
                                    let arg =
                                      let uu____15976 =
                                        FStar_Syntax_Syntax.as_implicit true in
                                      (varg, uu____15976) in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits in
                                    let uu____15984 =
                                      let uu____16027 =
                                        let uu____16046 =
                                          let uu____16063 =
                                            let uu____16064 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_All.pipe_right uu____16064
                                              FStar_TypeChecker_Common.lcomp_of_comp in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____16063) in
                                        uu____16046 :: outargs in
                                      (subst1, uu____16027, (arg ::
                                        arg_rets), guard, fvs) in
                                    tc_args head_info uu____15984 rest args1))
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau_or_attr))::rest,
                         (uu____16134, FStar_Pervasives_Native.None)::uu____16135)
                          ->
                          let uu____16194 =
                            match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let tau1 = FStar_Syntax_Subst.subst subst tau in
                                let uu____16207 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau1 in
                                (match uu____16207 with
                                 | (tau2, uu____16219, g_tau) ->
                                     let uu____16221 =
                                       let uu____16222 =
                                         let uu____16229 =
                                           FStar_Dyn.mkdyn env in
                                         (uu____16229, tau2) in
                                       FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                         uu____16222 in
                                     (uu____16221, g_tau))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let attr1 =
                                  FStar_Syntax_Subst.subst subst attr in
                                let uu____16236 =
                                  tc_tot_or_gtot_term env attr1 in
                                (match uu____16236 with
                                 | (attr2, uu____16248, g_attr) ->
                                     ((FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                         attr2), g_attr)) in
                          (match uu____16194 with
                           | (ctx_uvar_meta, g_tau_or_attr) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____16259 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head) env
                                   fvs t in
                               (match uu____16259 with
                                | (t1, g_ex) ->
                                    let r1 =
                                      match outargs with
                                      | [] -> head.FStar_Syntax_Syntax.pos
                                      | ((t2, uu____16290), uu____16291,
                                         uu____16292)::uu____16293 ->
                                          let uu____16348 =
                                            FStar_Range.def_range
                                              head.FStar_Syntax_Syntax.pos in
                                          let uu____16349 =
                                            let uu____16350 =
                                              FStar_Range.use_range
                                                head.FStar_Syntax_Syntax.pos in
                                            let uu____16351 =
                                              FStar_Range.use_range
                                                t2.FStar_Syntax_Syntax.pos in
                                            FStar_Range.union_rng uu____16350
                                              uu____16351 in
                                          FStar_Range.range_of_rng
                                            uu____16348 uu____16349 in
                                    let uu____16352 =
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        r1 env t1 FStar_Syntax_Syntax.Strict
                                        (FStar_Pervasives_Native.Some
                                           ctx_uvar_meta) in
                                    (match uu____16352 with
                                     | (varg, uu____16372, implicits) ->
                                         let subst1 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst in
                                         let arg =
                                           let uu____16400 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true in
                                           (varg, uu____16400) in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau_or_attr]
                                             implicits in
                                         let uu____16408 =
                                           let uu____16451 =
                                             let uu____16470 =
                                               let uu____16487 =
                                                 let uu____16488 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1 in
                                                 FStar_All.pipe_right
                                                   uu____16488
                                                   FStar_TypeChecker_Common.lcomp_of_comp in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16487) in
                                             uu____16470 :: outargs in
                                           (subst1, uu____16451, (arg ::
                                             arg_rets), guard, fvs) in
                                         tc_args head_info uu____16408 rest
                                           args1)))
                      | ((x, aqual)::rest, (e, aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16628, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16629)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16636),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16637)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16642),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16643)) ->
                                ()
                            | (FStar_Pervasives_Native.None,
                               FStar_Pervasives_Native.None) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality),
                               FStar_Pervasives_Native.None) -> ()
                            | uu____16656 ->
                                let uu____16665 =
                                  let uu____16670 =
                                    let uu____16671 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual in
                                    let uu____16672 =
                                      FStar_Syntax_Print.aqual_to_string aq in
                                    let uu____16673 =
                                      FStar_Syntax_Print.bv_to_string x in
                                    let uu____16674 =
                                      FStar_Syntax_Print.term_to_string e in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____16671 uu____16672 uu____16673
                                      uu____16674 in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____16670) in
                                FStar_Errors.raise_error uu____16665
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst aqual in
                            let x1 =
                              let uu___2354_16678 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2354_16678.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2354_16678.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____16680 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____16680
                             then
                               let uu____16681 =
                                 FStar_Syntax_Print.bv_to_string x1 in
                               let uu____16682 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort in
                               let uu____16683 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____16684 =
                                 FStar_Syntax_Print.subst_to_string subst in
                               let uu____16685 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____16681 uu____16682 uu____16683
                                 uu____16684 uu____16685
                             else ());
                            (let uu____16687 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head) env fvs
                                 targ in
                             match uu____16687 with
                             | (targ1, g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1 in
                                 let env2 =
                                   let uu___2363_16702 = env1 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2363_16702.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2363_16702.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2363_16702.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2363_16702.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2363_16702.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2363_16702.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2363_16702.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2363_16702.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2363_16702.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2363_16702.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2363_16702.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2363_16702.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2363_16702.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2363_16702.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2363_16702.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2363_16702.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___2363_16702.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2363_16702.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2363_16702.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2363_16702.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2363_16702.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2363_16702.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2363_16702.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2363_16702.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2363_16702.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2363_16702.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2363_16702.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2363_16702.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2363_16702.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2363_16702.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2363_16702.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2363_16702.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2363_16702.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2363_16702.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2363_16702.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2363_16702.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2363_16702.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2363_16702.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2363_16702.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2363_16702.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2363_16702.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2363_16702.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2363_16702.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2363_16702.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2363_16702.FStar_TypeChecker_Env.erasable_types_tab);
                                     FStar_TypeChecker_Env.enable_defer_to_tac
                                       =
                                       (uu___2363_16702.FStar_TypeChecker_Env.enable_defer_to_tac)
                                   } in
                                 ((let uu____16704 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High in
                                   if uu____16704
                                   then
                                     let uu____16705 =
                                       FStar_Syntax_Print.tag_of_term e in
                                     let uu____16706 =
                                       FStar_Syntax_Print.term_to_string e in
                                     let uu____16707 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1 in
                                     let uu____16708 =
                                       FStar_Util.string_of_bool
                                         env2.FStar_TypeChecker_Env.use_eq in
                                     FStar_Util.print4
                                       "Checking arg (%s) %s at type %s with use_eq:%s\n"
                                       uu____16705 uu____16706 uu____16707
                                       uu____16708
                                   else ());
                                  (let uu____16710 = tc_term env2 e in
                                   match uu____16710 with
                                   | (e1, c, g_e) ->
                                       let g1 =
                                         let uu____16727 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____16727 in
                                       let arg = (e1, aq) in
                                       let xterm =
                                         let uu____16750 =
                                           let uu____16753 =
                                             let uu____16762 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16762 in
                                           FStar_Pervasives_Native.fst
                                             uu____16753 in
                                         (uu____16750, aq) in
                                       let uu____16771 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name) in
                                       if uu____16771
                                       then
                                         let subst1 =
                                           let uu____16779 = FStar_List.hd bs in
                                           maybe_extend_subst subst
                                             uu____16779 e1 in
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
                      | (uu____16925, []) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([], arg::uu____16961) ->
                          let uu____17012 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs [] in
                          (match uu____17012 with
                           | (head1, chead1, ghead1) ->
                               let uu____17034 =
                                 let uu____17039 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1 in
                                 FStar_All.pipe_right uu____17039
                                   (fun uu____17056 ->
                                      match uu____17056 with
                                      | (c, g1) ->
                                          let uu____17067 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1 in
                                          (c, uu____17067)) in
                               (match uu____17034 with
                                | (chead2, ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____17106 =
                                          FStar_Syntax_Subst.compress tres in
                                        FStar_All.pipe_right uu____17106
                                          FStar_Syntax_Util.unrefine in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1, cres') ->
                                          let uu____17137 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres' in
                                          (match uu____17137 with
                                           | (bs2, cres'1) ->
                                               let head_info1 =
                                                 (head1, chead2, ghead3,
                                                   cres'1) in
                                               ((let uu____17160 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low in
                                                 if uu____17160
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
                                      | uu____17218 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____17226 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env) in
                                              FStar_All.pipe_right
                                                uu____17226
                                                FStar_Syntax_Util.unascribe in
                                            let uu____17227 =
                                              let uu____17228 =
                                                FStar_Syntax_Subst.compress
                                                  tres3 in
                                              uu____17228.FStar_Syntax_Syntax.n in
                                            match uu____17227 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____17231;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____17232;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},
                                                 uu____17234)
                                                -> norm_tres tres4
                                            | uu____17241 -> tres3 in
                                          let uu____17242 = norm_tres tres1 in
                                          aux true solve ghead3 uu____17242
                                      | uu____17243 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3 in
                                          aux norm1 true ghead4 tres1
                                      | uu____17245 ->
                                          let uu____17246 =
                                            let uu____17251 =
                                              let uu____17252 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead in
                                              let uu____17253 =
                                                FStar_Util.string_of_int
                                                  n_args in
                                              let uu____17254 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____17252 uu____17253
                                                uu____17254 in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____17251) in
                                          let uu____17255 =
                                            FStar_Syntax_Syntax.argpos arg in
                                          FStar_Errors.raise_error
                                            uu____17246 uu____17255 in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2)))) in
               let rec check_function_app tf guard =
                 let uu____17283 =
                   let uu____17284 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____17284.FStar_Syntax_Syntax.n in
                 match uu____17283 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____17293 ->
                     let uu____17306 =
                       FStar_List.fold_right
                         (fun uu____17337 ->
                            fun uu____17338 ->
                              match uu____17338 with
                              | (bs, guard1) ->
                                  let uu____17365 =
                                    let uu____17378 =
                                      let uu____17379 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____17379
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17378 in
                                  (match uu____17365 with
                                   | (t, uu____17395, g) ->
                                       let uu____17409 =
                                         let uu____17412 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____17412 :: bs in
                                       let uu____17413 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____17409, uu____17413))) args
                         ([], guard) in
                     (match uu____17306 with
                      | (bs, guard1) ->
                          let uu____17430 =
                            let uu____17437 =
                              let uu____17450 =
                                let uu____17451 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____17451
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17450 in
                            match uu____17437 with
                            | (t, uu____17467, g) ->
                                let uu____17481 = FStar_Options.ml_ish () in
                                if uu____17481
                                then
                                  let uu____17488 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____17491 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____17488, uu____17491)
                                else
                                  (let uu____17495 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____17498 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____17495, uu____17498)) in
                          (match uu____17430 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____17517 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____17517
                                 then
                                   let uu____17518 =
                                     FStar_Syntax_Print.term_to_string head in
                                   let uu____17519 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____17520 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17518 uu____17519 uu____17520
                                 else ());
                                (let g =
                                   let uu____17523 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17523 in
                                 let uu____17524 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____17524))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17525;
                        FStar_Syntax_Syntax.pos = uu____17526;
                        FStar_Syntax_Syntax.vars = uu____17527;_},
                      uu____17528)
                     ->
                     let uu____17565 =
                       FStar_List.fold_right
                         (fun uu____17596 ->
                            fun uu____17597 ->
                              match uu____17597 with
                              | (bs, guard1) ->
                                  let uu____17624 =
                                    let uu____17637 =
                                      let uu____17638 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____17638
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17637 in
                                  (match uu____17624 with
                                   | (t, uu____17654, g) ->
                                       let uu____17668 =
                                         let uu____17671 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____17671 :: bs in
                                       let uu____17672 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____17668, uu____17672))) args
                         ([], guard) in
                     (match uu____17565 with
                      | (bs, guard1) ->
                          let uu____17689 =
                            let uu____17696 =
                              let uu____17709 =
                                let uu____17710 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____17710
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17709 in
                            match uu____17696 with
                            | (t, uu____17726, g) ->
                                let uu____17740 = FStar_Options.ml_ish () in
                                if uu____17740
                                then
                                  let uu____17747 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____17750 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____17747, uu____17750)
                                else
                                  (let uu____17754 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____17757 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____17754, uu____17757)) in
                          (match uu____17689 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____17776 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____17776
                                 then
                                   let uu____17777 =
                                     FStar_Syntax_Print.term_to_string head in
                                   let uu____17778 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____17779 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17777 uu____17778 uu____17779
                                 else ());
                                (let g =
                                   let uu____17782 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17782 in
                                 let uu____17783 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____17783))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                     let uu____17806 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____17806 with
                      | (bs1, c1) ->
                          let head_info = (head, chead, ghead, c1) in
                          ((let uu____17829 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme in
                            if uu____17829
                            then
                              let uu____17830 =
                                FStar_Syntax_Print.term_to_string head in
                              let uu____17831 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____17832 =
                                FStar_Syntax_Print.binders_to_string ", " bs1 in
                              let uu____17833 =
                                FStar_Syntax_Print.comp_to_string c1 in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17830 uu____17831 uu____17832
                                uu____17833
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv, uu____17892) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t, uu____17898, uu____17899) ->
                     check_function_app t guard
                 | uu____17940 ->
                     let uu____17941 =
                       FStar_TypeChecker_Err.expected_function_typ env tf in
                     FStar_Errors.raise_error uu____17941
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
                  let uu____18023 =
                    FStar_List.fold_left2
                      (fun uu____18090 ->
                         fun uu____18091 ->
                           fun uu____18092 ->
                             match (uu____18090, uu____18091, uu____18092)
                             with
                             | ((seen, guard, ghost), (e, aq), (b, aq')) ->
                                 ((let uu____18239 =
                                     let uu____18240 =
                                       FStar_Syntax_Util.eq_aqual aq aq' in
                                     uu____18240 <> FStar_Syntax_Util.Equal in
                                   if uu____18239
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____18242 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                       "arguments to short circuiting operators must be pure or ghost" in
                                   match uu____18242 with
                                   | (e1, c1, g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen in
                                       let g1 =
                                         let uu____18270 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____18270 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____18274 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____18274)
                                              &&
                                              (let uu____18276 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name in
                                               Prims.op_Negation uu____18276)) in
                                       let uu____18277 =
                                         let uu____18288 =
                                           let uu____18299 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____18299] in
                                         FStar_List.append seen uu____18288 in
                                       let uu____18332 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1 in
                                       (uu____18277, uu____18332, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____18023 with
                   | (args1, guard, ghost) ->
                       let e = FStar_Syntax_Syntax.mk_Tm_app head args1 r in
                       let c1 =
                         if ghost
                         then
                           let uu____18392 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____18392
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c in
                       let uu____18394 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____18394 with | (c2, g) -> (e, c2, g)))
              | uu____18410 ->
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
            let uu____18502 = FStar_Syntax_Util.head_and_args t1 in
            match uu____18502 with
            | (head, args) ->
                let uu____18545 =
                  let uu____18546 = FStar_Syntax_Subst.compress head in
                  uu____18546.FStar_Syntax_Syntax.n in
                (match uu____18545 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18550;
                        FStar_Syntax_Syntax.vars = uu____18551;_},
                      us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18558 ->
                     if norm1
                     then t1
                     else
                       (let uu____18560 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1 in
                        aux true uu____18560))
          and unfold_once t f us args =
            let uu____18577 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            if uu____18577
            then t
            else
              (let uu____18579 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               match uu____18579 with
               | FStar_Pervasives_Native.None -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____18599 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
                   (match uu____18599 with
                    | (uu____18604, head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            t.FStar_Syntax_Syntax.pos in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t' in
                        aux false t'1)) in
          let uu____18608 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t in
          aux false uu____18608 in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____18626 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____18626
           then
             let uu____18627 = FStar_Syntax_Print.term_to_string pat_t1 in
             let uu____18628 = FStar_Syntax_Print.term_to_string scrutinee_t in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____18627 uu____18628
           else ());
          (let fail1 msg =
             let msg1 =
               let uu____18642 = FStar_Syntax_Print.term_to_string pat_t1 in
               let uu____18643 =
                 FStar_Syntax_Print.term_to_string scrutinee_t in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____18642 uu____18643 msg in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p in
           let uu____18644 = FStar_Syntax_Util.head_and_args scrutinee_t in
           match uu____18644 with
           | (head_s, args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1 in
               let uu____18688 = FStar_Syntax_Util.un_uinst head_s in
               (match uu____18688 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____18689;
                    FStar_Syntax_Syntax.pos = uu____18690;
                    FStar_Syntax_Syntax.vars = uu____18691;_} ->
                    let uu____18694 = FStar_Syntax_Util.head_and_args pat_t2 in
                    (match uu____18694 with
                     | (head_p, args_p) ->
                         let uu____18737 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s in
                         if uu____18737
                         then
                           let uu____18738 =
                             let uu____18739 =
                               FStar_Syntax_Util.un_uinst head_p in
                             uu____18739.FStar_Syntax_Syntax.n in
                           (match uu____18738 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____18744 =
                                    let uu____18745 =
                                      let uu____18746 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____18746 in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____18745 in
                                  if uu____18744
                                  then
                                    fail1
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail1 ""
                                 else ();
                                 (let uu____18766 =
                                    let uu____18791 =
                                      let uu____18794 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18794 in
                                    match uu____18791 with
                                    | FStar_Pervasives_Native.None ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n ->
                                        let uu____18840 =
                                          FStar_Util.first_N n args_p in
                                        (match uu____18840 with
                                         | (params_p, uu____18898) ->
                                             let uu____18939 =
                                               FStar_Util.first_N n args_s in
                                             (match uu____18939 with
                                              | (params_s, uu____18997) ->
                                                  (params_p, params_s))) in
                                  match uu____18766 with
                                  | (params_p, params_s) ->
                                      FStar_List.fold_left2
                                        (fun out ->
                                           fun uu____19126 ->
                                             fun uu____19127 ->
                                               match (uu____19126,
                                                       uu____19127)
                                               with
                                               | ((p, uu____19161),
                                                  (s, uu____19163)) ->
                                                   let uu____19196 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s in
                                                   (match uu____19196 with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        let uu____19199 =
                                                          let uu____19200 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p in
                                                          let uu____19201 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____19200
                                                            uu____19201 in
                                                        fail1 uu____19199
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____19204 ->
                                fail1 "Pattern matching a non-inductive type")
                         else
                           (let uu____19206 =
                              let uu____19207 =
                                FStar_Syntax_Print.term_to_string head_p in
                              let uu____19208 =
                                FStar_Syntax_Print.term_to_string head_s in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____19207 uu____19208 in
                            fail1 uu____19206))
                | uu____19209 ->
                    let uu____19210 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t in
                    (match uu____19210 with
                     | FStar_Pervasives_Native.None -> fail1 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g in
                         g1))) in
        let type_of_simple_pat env1 e =
          let uu____19250 = FStar_Syntax_Util.head_and_args e in
          match uu____19250 with
          | (head, args) ->
              (match head.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____19318 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____19318 with
                    | (us, t_f) ->
                        let uu____19337 = FStar_Syntax_Util.arrow_formals t_f in
                        (match uu____19337 with
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
                              (let rec aux uu____19442 formals1 args1 =
                                 match uu____19442 with
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
                                          let uu____19585 =
                                            FStar_Syntax_Subst.subst subst t in
                                          (pat_e, uu____19585, bvs, guard,
                                            erasable)
                                      | ((f1, uu____19589)::formals2,
                                         (a, imp_a)::args2) ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst
                                              f1.FStar_Syntax_Syntax.sort in
                                          let uu____19647 =
                                            let uu____19668 =
                                              let uu____19669 =
                                                FStar_Syntax_Subst.compress a in
                                              uu____19669.FStar_Syntax_Syntax.n in
                                            match uu____19668 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2670_19694 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2670_19694.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2670_19694.FStar_Syntax_Syntax.index);
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
                                                uu____19717 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1 in
                                                let uu____19731 =
                                                  tc_tot_or_gtot_term env2 a in
                                                (match uu____19731 with
                                                 | (a1, uu____19759, g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g in
                                                     let subst1 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst in
                                                     ((a1, imp_a), subst1,
                                                       bvs, g1))
                                            | uu____19783 ->
                                                fail "Not a simple pattern" in
                                          (match uu____19647 with
                                           | (a1, subst1, bvs1, g) ->
                                               let uu____19844 =
                                                 let uu____19867 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard in
                                                 (subst1,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19867) in
                                               aux uu____19844 formals2 args2)
                                      | uu____19906 ->
                                          fail "Not a fully applued pattern") in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19961 -> fail "Not a simple pattern") in
        let rec check_nested_pattern env1 p t =
          (let uu____20023 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____20023
           then
             let uu____20024 = FStar_Syntax_Print.pat_to_string p in
             let uu____20025 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____20024
               uu____20025
           else ());
          (let id =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____20046 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t in
               FStar_All.pipe_right uu____20046 FStar_Syntax_Syntax.mk_binder in
             let tm =
               let uu____20054 =
                 let uu____20055 =
                   let uu____20064 =
                     let uu____20065 =
                       FStar_All.pipe_right x_b FStar_Pervasives_Native.fst in
                     FStar_All.pipe_right uu____20065
                       FStar_Syntax_Syntax.bv_to_name in
                   FStar_All.pipe_right uu____20064
                     FStar_Syntax_Syntax.as_arg in
                 [uu____20055] in
               FStar_Syntax_Syntax.mk_Tm_app disc uu____20054
                 FStar_Range.dummyRange in
             let tm1 =
               let uu____20099 =
                 let uu____20100 =
                   FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg in
                 [uu____20100] in
               FStar_Syntax_Syntax.mk_Tm_app inner_t uu____20099
                 FStar_Range.dummyRange in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____20161 ->
               let uu____20168 =
                 let uu____20169 = FStar_Syntax_Print.pat_to_string p in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____20169 in
               failwith uu____20168
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2709_20188 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2709_20188.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2709_20188.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____20189 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], [id], uu____20189,
                 (let uu___2712_20195 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2712_20195.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2716_20198 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2716_20198.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2716_20198.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____20199 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], [id], uu____20199,
                 (let uu___2719_20205 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2719_20205.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant uu____20206 ->
               let uu____20207 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p in
               (match uu____20207 with
                | (uu____20234, e_c, uu____20236, uu____20237) ->
                    let uu____20242 = tc_tot_or_gtot_term env1 e_c in
                    (match uu____20242 with
                     | (e_c1, lc, g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t in
                           (let uu____20271 =
                              let uu____20272 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t in
                              Prims.op_Negation uu____20272 in
                            if uu____20271
                            then
                              let uu____20273 =
                                let uu____20274 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ in
                                let uu____20275 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____20274 uu____20275 in
                              fail uu____20273
                            else ());
                           ([], [], e_c1, p,
                             FStar_TypeChecker_Env.trivial_guard, false)))))
           | FStar_Syntax_Syntax.Pat_cons (fv, sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20327 ->
                        match uu____20327 with
                        | (p1, b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____20352
                                 -> (p1, b)
                             | uu____20361 ->
                                 let uu____20362 =
                                   let uu____20365 =
                                     let uu____20366 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun in
                                     FStar_Syntax_Syntax.Pat_var uu____20366 in
                                   FStar_Syntax_Syntax.withinfo uu____20365
                                     p1.FStar_Syntax_Syntax.p in
                                 (uu____20362, b))) sub_pats in
                 let uu___2747_20369 = p in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2747_20369.FStar_Syntax_Syntax.p)
                 } in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____20409 ->
                         match uu____20409 with
                         | (x, uu____20417) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____20422
                                  -> false
                              | uu____20429 -> true))) in
               let uu____20430 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat in
               (match uu____20430 with
                | (simple_bvs, simple_pat_e, g0, simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____20470 =
                          let uu____20471 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p in
                          let uu____20472 =
                            FStar_Syntax_Print.pat_to_string simple_pat in
                          let uu____20473 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1) in
                          let uu____20478 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs) in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____20471 uu____20472 uu____20473 uu____20478 in
                        failwith uu____20470)
                     else ();
                     (let uu____20480 =
                        let uu____20491 =
                          type_of_simple_pat env1 simple_pat_e in
                        match uu____20491 with
                        | (simple_pat_e1, simple_pat_t, simple_bvs1, guard,
                           erasable) ->
                            let g' =
                              let uu____20524 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t in
                              pat_typ_ok env1 simple_pat_t uu____20524 in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g' in
                            ((let uu____20527 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns") in
                              if uu____20527
                              then
                                let uu____20528 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1 in
                                let uu____20529 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t in
                                let uu____20530 =
                                  let uu____20531 =
                                    FStar_List.map
                                      (fun x ->
                                         let uu____20537 =
                                           let uu____20538 =
                                             FStar_Syntax_Print.bv_to_string
                                               x in
                                           let uu____20539 =
                                             let uu____20540 =
                                               let uu____20541 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort in
                                               Prims.op_Hat uu____20541 ")" in
                                             Prims.op_Hat " : " uu____20540 in
                                           Prims.op_Hat uu____20538
                                             uu____20539 in
                                         Prims.op_Hat "(" uu____20537)
                                      simple_bvs1 in
                                  FStar_All.pipe_right uu____20531
                                    (FStar_String.concat " ") in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____20528 uu____20529 uu____20530
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable)) in
                      match uu____20480 with
                      | (simple_pat_e1, simple_bvs1, g1, erasable) ->
                          let uu____20571 =
                            let uu____20600 =
                              let uu____20629 =
                                FStar_TypeChecker_Env.conj_guard g0 g1 in
                              (env1, [], [], [], [], uu____20629, erasable,
                                Prims.int_zero) in
                            FStar_List.fold_left2
                              (fun uu____20702 ->
                                 fun uu____20703 ->
                                   fun x ->
                                     match (uu____20702, uu____20703) with
                                     | ((env2, bvs, tms, pats, subst, g,
                                         erasable1, i),
                                        (p1, b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst
                                             x.FStar_Syntax_Syntax.sort in
                                         let uu____20864 =
                                           check_nested_pattern env2 p1
                                             expected_t in
                                         (match uu____20864 with
                                          | (bvs_p, tms_p, e_p, p2, g',
                                             erasable_p) ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____20928 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____20928 i in
                                                let uu____20929 =
                                                  let uu____20938 =
                                                    let uu____20943 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None in
                                                    mk_disc_t uu____20943 in
                                                  FStar_List.map uu____20938 in
                                                FStar_All.pipe_right tms_p
                                                  uu____20929 in
                                              let uu____20948 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g' in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append tms tms_p1),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst),
                                                uu____20948,
                                                (erasable1 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____20600 sub_pats1 simple_bvs1 in
                          (match uu____20571 with
                           | (_env, bvs, tms, checked_sub_pats, subst, g,
                              erasable1, uu____20998) ->
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
                                              let uu___2831_21155 = hd in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2831_21155.FStar_Syntax_Syntax.p)
                                              } in
                                            let uu____21160 =
                                              aux simple_pats1 bvs1 sub_pats2 in
                                            (hd1, b) :: uu____21160
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,
                                                (hd1, uu____21199)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____21231 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3 in
                                                 (hd1, b) :: uu____21231
                                             | uu____21248 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____21271 ->
                                            failwith
                                              "Impossible: expected a simple pattern") in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1, simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats in
                                     let uu___2852_21309 = pat in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2852_21309.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____21320 -> failwith "Impossible" in
                               let uu____21323 =
                                 reconstruct_nested_pat simple_pat_elab in
                               (bvs, tms, pat_e, uu____21323, g, erasable1)))))) in
        (let uu____21329 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns") in
         if uu____21329
         then
           let uu____21330 = FStar_Syntax_Print.pat_to_string p0 in
           FStar_Util.print1 "Checking pattern: %s\n" uu____21330
         else ());
        (let uu____21332 =
           let uu____21349 =
             let uu___2857_21350 =
               let uu____21351 = FStar_TypeChecker_Env.clear_expected_typ env in
               FStar_All.pipe_right uu____21351 FStar_Pervasives_Native.fst in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2857_21350.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2857_21350.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2857_21350.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2857_21350.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2857_21350.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2857_21350.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2857_21350.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2857_21350.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2857_21350.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2857_21350.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2857_21350.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2857_21350.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2857_21350.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2857_21350.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2857_21350.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2857_21350.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___2857_21350.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2857_21350.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2857_21350.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2857_21350.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2857_21350.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2857_21350.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2857_21350.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2857_21350.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2857_21350.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2857_21350.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2857_21350.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2857_21350.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2857_21350.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2857_21350.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2857_21350.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2857_21350.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2857_21350.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2857_21350.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2857_21350.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2857_21350.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2857_21350.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2857_21350.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2857_21350.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2857_21350.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2857_21350.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2857_21350.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2857_21350.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2857_21350.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2857_21350.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___2857_21350.FStar_TypeChecker_Env.enable_defer_to_tac)
             } in
           let uu____21366 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0 in
           check_nested_pattern uu____21349 uu____21366 pat_t in
         match uu____21332 with
         | (bvs, tms, pat_e, pat, g, erasable) ->
             ((let uu____21402 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns") in
               if uu____21402
               then
                 let uu____21403 = FStar_Syntax_Print.pat_to_string pat in
                 let uu____21404 = FStar_Syntax_Print.term_to_string pat_e in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____21403
                   uu____21404
               else ());
              (let uu____21406 = FStar_TypeChecker_Env.push_bvs env bvs in
               let uu____21407 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e in
               (pat, bvs, tms, uu____21406, pat_e, uu____21407, g, erasable))))
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
        let uu____21442 = FStar_Syntax_Subst.open_branch branch in
        match uu____21442 with
        | (pattern, when_clause, branch_exp) ->
            let uu____21489 = branch in
            (match uu____21489 with
             | (cpat, uu____21518, cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____21540 =
                   let uu____21547 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____21547
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____21540 with
                  | (scrutinee_env, uu____21582) ->
                      let uu____21587 = tc_pat env pat_t pattern in
                      (match uu____21587 with
                       | (pattern1, pat_bvs, pat_bv_tms, pat_env, pat_exp,
                          norm_pat_exp, guard_pat, erasable) ->
                           ((let uu____21652 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme in
                             if uu____21652
                             then
                               let uu____21653 =
                                 FStar_Syntax_Print.pat_to_string pattern1 in
                               let uu____21654 =
                                 FStar_Syntax_Print.bvs_to_string ";" pat_bvs in
                               let uu____21655 =
                                 FStar_List.fold_left
                                   (fun s ->
                                      fun t ->
                                        let uu____21661 =
                                          let uu____21662 =
                                            FStar_Syntax_Print.term_to_string
                                              t in
                                          Prims.op_Hat ";" uu____21662 in
                                        Prims.op_Hat s uu____21661) ""
                                   pat_bv_tms in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____21653 uu____21654 uu____21655
                             else ());
                            (let uu____21664 =
                               match when_clause with
                               | FStar_Pervasives_Native.None ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____21694 =
                                     FStar_TypeChecker_Env.should_verify env in
                                   if uu____21694
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____21712 =
                                        let uu____21719 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool in
                                        tc_term uu____21719 e in
                                      match uu____21712 with
                                      | (e1, c, g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g)) in
                             match uu____21664 with
                             | (when_clause1, g_when) ->
                                 let uu____21774 = tc_term pat_env branch_exp in
                                 (match uu____21774 with
                                  | (branch_exp1, c, g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____21830 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool in
                                              FStar_All.pipe_left
                                                (fun uu____21841 ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____21841) uu____21830 in
                                        let branch_guard =
                                          let uu____21845 =
                                            let uu____21846 =
                                              FStar_TypeChecker_Env.should_verify
                                                env in
                                            Prims.op_Negation uu____21846 in
                                          if uu____21845
                                          then FStar_Syntax_Util.t_true
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____21899 =
                                                   let uu____21906 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____21906 in
                                                 match uu____21899 with
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
                                                       let uu____21918 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator in
                                                       (match uu____21918
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                            -> []
                                                        | uu____21939 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None in
                                                            let disc1 =
                                                              let uu____21952
                                                                =
                                                                let uu____21953
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2 in
                                                                [uu____21953] in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____21952
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                            let uu____21978 =
                                                              FStar_Syntax_Util.mk_eq2
                                                                FStar_Syntax_Syntax.U_zero
                                                                FStar_Syntax_Util.t_bool
                                                                disc1
                                                                FStar_Syntax_Util.exp_true_bool in
                                                            [uu____21978])
                                                     else [] in
                                               let fail uu____21985 =
                                                 let uu____21986 =
                                                   let uu____21987 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos in
                                                   let uu____21988 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1 in
                                                   let uu____21989 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1 in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____21987 uu____21988
                                                     uu____21989 in
                                                 failwith uu____21986 in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1, uu____22002) ->
                                                     head_constructor t1
                                                 | uu____22007 -> fail () in
                                               let force_scrutinee
                                                 uu____22013 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     let uu____22014 =
                                                       let uu____22015 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p in
                                                       let uu____22016 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2 in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____22015
                                                         uu____22016 in
                                                     failwith uu____22014
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t in
                                               let pat_exp2 =
                                                 let uu____22021 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1 in
                                                 FStar_All.pipe_right
                                                   uu____22021
                                                   FStar_Syntax_Util.unmeta in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____22026,
                                                  FStar_Syntax_Syntax.Tm_name
                                                  uu____22027) -> []
                                               | (uu____22028,
                                                  FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,
                                                  FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____22031 =
                                                     let uu____22032 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1 in
                                                     let uu____22033 =
                                                       force_scrutinee () in
                                                     FStar_Syntax_Util.mk_eq2
                                                       FStar_Syntax_Syntax.U_zero
                                                       uu____22032
                                                       uu____22033 pat_exp2 in
                                                   [uu____22031]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____22034,
                                                   FStar_Pervasives_Native.Some
                                                   uu____22035)),
                                                  uu____22036) ->
                                                   let uu____22051 =
                                                     let uu____22058 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env in
                                                     match uu____22058 with
                                                     | (env1, uu____22072) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2 in
                                                   (match uu____22051 with
                                                    | (uu____22079, t,
                                                       uu____22081) ->
                                                        let uu____22082 =
                                                          let uu____22083 =
                                                            force_scrutinee
                                                              () in
                                                          FStar_Syntax_Util.mk_eq2
                                                            FStar_Syntax_Syntax.U_zero
                                                            t uu____22083
                                                            pat_exp2 in
                                                        [uu____22082])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22084, []),
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                  uu____22085) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2 in
                                                   let uu____22107 =
                                                     let uu____22108 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v in
                                                     Prims.op_Negation
                                                       uu____22108 in
                                                   if uu____22107
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22114 =
                                                        force_scrutinee () in
                                                      let uu____22117 =
                                                        head_constructor
                                                          pat_exp2 in
                                                      discriminate
                                                        uu____22114
                                                        uu____22117)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22120, []),
                                                  FStar_Syntax_Syntax.Tm_fvar
                                                  uu____22121) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2 in
                                                   let uu____22137 =
                                                     let uu____22138 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v in
                                                     Prims.op_Negation
                                                       uu____22138 in
                                                   if uu____22137
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22144 =
                                                        force_scrutinee () in
                                                      let uu____22147 =
                                                        head_constructor
                                                          pat_exp2 in
                                                      discriminate
                                                        uu____22144
                                                        uu____22147)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22150, pat_args),
                                                  FStar_Syntax_Syntax.Tm_app
                                                  (head, args)) ->
                                                   let f =
                                                     head_constructor head in
                                                   let uu____22195 =
                                                     (let uu____22198 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v in
                                                      Prims.op_Negation
                                                        uu____22198)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args)) in
                                                   if uu____22195
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____22221 =
                                                          let uu____22226 =
                                                            FStar_List.zip
                                                              pat_args args in
                                                          FStar_All.pipe_right
                                                            uu____22226
                                                            (FStar_List.mapi
                                                               (fun i ->
                                                                  fun
                                                                    uu____22308
                                                                    ->
                                                                    match uu____22308
                                                                    with
                                                                    | 
                                                                    ((pi,
                                                                    uu____22328),
                                                                    (ei,
                                                                    uu____22330))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____22355
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    match uu____22355
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____22376
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____22388
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____22388
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____22389
                                                                    =
                                                                    let uu____22390
                                                                    =
                                                                    let uu____22391
                                                                    =
                                                                    let uu____22400
                                                                    =
                                                                    force_scrutinee
                                                                    () in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____22400 in
                                                                    [uu____22391] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____22390
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____22389 in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei)) in
                                                        FStar_All.pipe_right
                                                          uu____22221
                                                          FStar_List.flatten in
                                                      let uu____22423 =
                                                        let uu____22426 =
                                                          force_scrutinee () in
                                                        discriminate
                                                          uu____22426 f in
                                                      FStar_List.append
                                                        uu____22423
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____22429, uu____22430)
                                                   -> []
                                               | uu____22437 ->
                                                   let uu____22442 =
                                                     let uu____22443 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2 in
                                                     let uu____22444 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2 in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____22443
                                                       uu____22444 in
                                                   failwith uu____22442 in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____22471 =
                                                 let uu____22472 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____22472 in
                                               if uu____22471
                                               then
                                                 FStar_TypeChecker_Util.fvar_const
                                                   env
                                                   FStar_Parser_Const.true_lid
                                               else
                                                 (let t =
                                                    let uu____22475 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_conj_l
                                                      uu____22475 in
                                                  let uu____22484 =
                                                    FStar_Syntax_Util.type_u
                                                      () in
                                                  match uu____22484 with
                                                  | (k, uu____22490) ->
                                                      let uu____22491 =
                                                        tc_check_tot_or_gtot_term
                                                          scrutinee_env t k
                                                          "" in
                                                      (match uu____22491 with
                                                       | (t1, uu____22499,
                                                          uu____22500) -> t1)) in
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
                                                   FStar_Syntax_Util.mk_conj
                                                     branch_guard w in
                                             branch_guard1) in
                                        let uu____22514 =
                                          let eqs =
                                            let uu____22533 =
                                              let uu____22534 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____22534 in
                                            if uu____22533
                                            then FStar_Pervasives_Native.None
                                            else
                                              (let e =
                                                 FStar_Syntax_Subst.compress
                                                   pat_exp in
                                               let uu____22539 =
                                                 let uu____22540 =
                                                   env.FStar_TypeChecker_Env.universe_of
                                                     env pat_t in
                                                 FStar_Syntax_Util.mk_eq2
                                                   uu____22540 pat_t
                                                   scrutinee_tm e in
                                               FStar_Pervasives_Native.Some
                                                 uu____22539) in
                                          let uu____22541 =
                                            FStar_TypeChecker_Util.strengthen_precondition
                                              FStar_Pervasives_Native.None
                                              env branch_exp1 c g_branch in
                                          match uu____22541 with
                                          | (c1, g_branch1) ->
                                              let branch_has_layered_effect =
                                                let uu____22567 =
                                                  FStar_All.pipe_right
                                                    c1.FStar_TypeChecker_Common.eff_name
                                                    (FStar_TypeChecker_Env.norm_eff_name
                                                       env) in
                                                FStar_All.pipe_right
                                                  uu____22567
                                                  (FStar_TypeChecker_Env.is_layered_effect
                                                     env) in
                                              let uu____22568 =
                                                let env1 =
                                                  let uu____22574 =
                                                    FStar_All.pipe_right
                                                      pat_bvs
                                                      (FStar_List.map
                                                         FStar_Syntax_Syntax.mk_binder) in
                                                  FStar_TypeChecker_Env.push_binders
                                                    scrutinee_env uu____22574 in
                                                if branch_has_layered_effect
                                                then
                                                  let c2 =
                                                    FStar_TypeChecker_Util.weaken_precondition
                                                      env1 c1
                                                      (FStar_TypeChecker_Common.NonTrivial
                                                         branch_guard) in
                                                  (c2,
                                                    FStar_TypeChecker_Env.trivial_guard)
                                                else
                                                  (match (eqs,
                                                           when_condition)
                                                   with
                                                   | uu____22593 when
                                                       let uu____22604 =
                                                         FStar_TypeChecker_Env.should_verify
                                                           env1 in
                                                       Prims.op_Negation
                                                         uu____22604
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
                                                       let uu____22624 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 gf in
                                                       let uu____22625 =
                                                         FStar_TypeChecker_Env.imp_guard
                                                           g g_when in
                                                       (uu____22624,
                                                         uu____22625)
                                                   | (FStar_Pervasives_Native.Some
                                                      f,
                                                      FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_f =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           f in
                                                       let g_fw =
                                                         let uu____22640 =
                                                           FStar_Syntax_Util.mk_conj
                                                             f w in
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           uu____22640 in
                                                       let uu____22641 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_fw in
                                                       let uu____22642 =
                                                         let uu____22643 =
                                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                                             g_f in
                                                         FStar_TypeChecker_Env.imp_guard
                                                           uu____22643 g_when in
                                                       (uu____22641,
                                                         uu____22642)
                                                   | (FStar_Pervasives_Native.None,
                                                      FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_w =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           w in
                                                       let g =
                                                         FStar_TypeChecker_Env.guard_of_guard_formula
                                                           g_w in
                                                       let uu____22657 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_w in
                                                       (uu____22657, g_when)) in
                                              (match uu____22568 with
                                               | (c_weak, g_when_weak) ->
                                                   let binders =
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder
                                                       pat_bvs in
                                                   let maybe_return_c_weak
                                                     should_return =
                                                     let c_weak1 =
                                                       let uu____22697 =
                                                         should_return &&
                                                           (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                              c_weak) in
                                                       if uu____22697
                                                       then
                                                         FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                           env branch_exp1
                                                           c_weak
                                                       else c_weak in
                                                     if
                                                       branch_has_layered_effect
                                                     then
                                                       ((let uu____22700 =
                                                           FStar_All.pipe_left
                                                             (FStar_TypeChecker_Env.debug
                                                                env)
                                                             (FStar_Options.Other
                                                                "LayeredEffects") in
                                                         if uu____22700
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
                                                                   let uu____22712
                                                                    =
                                                                    let uu____22713
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    [uu____22713] in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____22712
                                                                    FStar_Range.dummyRange)) in
                                                         let pat_bv_tms2 =
                                                           let env1 =
                                                             let uu___3090_22750
                                                               =
                                                               FStar_TypeChecker_Env.push_bv
                                                                 env
                                                                 scrutinee in
                                                             {
                                                               FStar_TypeChecker_Env.solver
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.solver);
                                                               FStar_TypeChecker_Env.range
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.range);
                                                               FStar_TypeChecker_Env.curmodule
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.curmodule);
                                                               FStar_TypeChecker_Env.gamma
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.gamma);
                                                               FStar_TypeChecker_Env.gamma_sig
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.gamma_sig);
                                                               FStar_TypeChecker_Env.gamma_cache
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.gamma_cache);
                                                               FStar_TypeChecker_Env.modules
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.modules);
                                                               FStar_TypeChecker_Env.expected_typ
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.expected_typ);
                                                               FStar_TypeChecker_Env.sigtab
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.sigtab);
                                                               FStar_TypeChecker_Env.attrtab
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.attrtab);
                                                               FStar_TypeChecker_Env.instantiate_imp
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.instantiate_imp);
                                                               FStar_TypeChecker_Env.effects
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.effects);
                                                               FStar_TypeChecker_Env.generalize
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.generalize);
                                                               FStar_TypeChecker_Env.letrecs
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.letrecs);
                                                               FStar_TypeChecker_Env.top_level
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.top_level);
                                                               FStar_TypeChecker_Env.check_uvars
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.check_uvars);
                                                               FStar_TypeChecker_Env.use_eq
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.use_eq);
                                                               FStar_TypeChecker_Env.use_eq_strict
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.use_eq_strict);
                                                               FStar_TypeChecker_Env.is_iface
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.is_iface);
                                                               FStar_TypeChecker_Env.admit
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.admit);
                                                               FStar_TypeChecker_Env.lax
                                                                 = true;
                                                               FStar_TypeChecker_Env.lax_universes
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.lax_universes);
                                                               FStar_TypeChecker_Env.phase1
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.phase1);
                                                               FStar_TypeChecker_Env.failhard
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.failhard);
                                                               FStar_TypeChecker_Env.nosynth
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.nosynth);
                                                               FStar_TypeChecker_Env.uvar_subtyping
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.uvar_subtyping);
                                                               FStar_TypeChecker_Env.tc_term
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.tc_term);
                                                               FStar_TypeChecker_Env.type_of
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.type_of);
                                                               FStar_TypeChecker_Env.universe_of
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.universe_of);
                                                               FStar_TypeChecker_Env.check_type_of
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.check_type_of);
                                                               FStar_TypeChecker_Env.use_bv_sorts
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.use_bv_sorts);
                                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                               FStar_TypeChecker_Env.normalized_eff_names
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.normalized_eff_names);
                                                               FStar_TypeChecker_Env.fv_delta_depths
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.fv_delta_depths);
                                                               FStar_TypeChecker_Env.proof_ns
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.proof_ns);
                                                               FStar_TypeChecker_Env.synth_hook
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.synth_hook);
                                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                               FStar_TypeChecker_Env.splice
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.splice);
                                                               FStar_TypeChecker_Env.mpreprocess
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.mpreprocess);
                                                               FStar_TypeChecker_Env.postprocess
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.postprocess);
                                                               FStar_TypeChecker_Env.identifier_info
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.identifier_info);
                                                               FStar_TypeChecker_Env.tc_hooks
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.tc_hooks);
                                                               FStar_TypeChecker_Env.dsenv
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.dsenv);
                                                               FStar_TypeChecker_Env.nbe
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.nbe);
                                                               FStar_TypeChecker_Env.strict_args_tab
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.strict_args_tab);
                                                               FStar_TypeChecker_Env.erasable_types_tab
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.erasable_types_tab);
                                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                                 =
                                                                 (uu___3090_22750.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                             } in
                                                           let uu____22751 =
                                                             let uu____22754
                                                               =
                                                               FStar_List.fold_left2
                                                                 (fun
                                                                    uu____22782
                                                                    ->
                                                                    fun
                                                                    pat_bv_tm
                                                                    ->
                                                                    fun bv ->
                                                                    match uu____22782
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
                                                                    let uu____22823
                                                                    =
                                                                    let uu____22830
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pat_bv_tm
                                                                    (FStar_Syntax_Subst.subst
                                                                    substs) in
                                                                    let uu____22831
                                                                    =
                                                                    let uu____22842
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t in
                                                                    tc_trivial_guard
                                                                    uu____22842 in
                                                                    FStar_All.pipe_right
                                                                    uu____22830
                                                                    uu____22831 in
                                                                    FStar_All.pipe_right
                                                                    uu____22823
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
                                                               uu____22754
                                                               FStar_Pervasives_Native.snd in
                                                           FStar_All.pipe_right
                                                             uu____22751
                                                             (FStar_List.map
                                                                (FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Env.Beta]
                                                                   env1)) in
                                                         (let uu____22904 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects") in
                                                          if uu____22904
                                                          then
                                                            let uu____22905 =
                                                              FStar_List.fold_left
                                                                (fun s ->
                                                                   fun t ->
                                                                    let uu____22911
                                                                    =
                                                                    let uu____22912
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____22912 in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____22911)
                                                                ""
                                                                pat_bv_tms2 in
                                                            let uu____22913 =
                                                              FStar_List.fold_left
                                                                (fun s ->
                                                                   fun t ->
                                                                    let uu____22919
                                                                    =
                                                                    let uu____22920
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____22920 in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____22919)
                                                                "" pat_bvs in
                                                            FStar_Util.print2
                                                              "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                                                              uu____22905
                                                              uu____22913
                                                          else ());
                                                         (let uu____22922 =
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
                                                          let uu____22929 =
                                                            let uu____22934 =
                                                              FStar_TypeChecker_Env.push_bv
                                                                env scrutinee in
                                                            FStar_TypeChecker_Util.close_layered_lcomp
                                                              uu____22934
                                                              pat_bvs
                                                              pat_bv_tms2 in
                                                          FStar_All.pipe_right
                                                            uu____22922
                                                            uu____22929)))
                                                     else
                                                       FStar_TypeChecker_Util.close_wp_lcomp
                                                         env pat_bvs c_weak1 in
                                                   let uu____22936 =
                                                     FStar_TypeChecker_Env.close_guard
                                                       env binders
                                                       g_when_weak in
                                                   let uu____22937 =
                                                     FStar_TypeChecker_Env.conj_guard
                                                       guard_pat g_branch1 in
                                                   ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                     (c_weak.FStar_TypeChecker_Common.cflags),
                                                     maybe_return_c_weak,
                                                     uu____22936,
                                                     uu____22937)) in
                                        match uu____22514 with
                                        | (effect_label, cflags,
                                           maybe_return_c, g_when1,
                                           g_branch1) ->
                                            let guard =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_when1 g_branch1 in
                                            ((let uu____22987 =
                                                FStar_TypeChecker_Env.debug
                                                  env FStar_Options.High in
                                              if uu____22987
                                              then
                                                let uu____22988 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____22988
                                              else ());
                                             (let uu____22990 =
                                                FStar_Syntax_Subst.close_branch
                                                  (pattern1, when_clause1,
                                                    branch_exp1) in
                                              let uu____23007 =
                                                let uu____23008 =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs in
                                                FStar_TypeChecker_Util.close_guard_implicits
                                                  env false uu____23008 guard in
                                              (uu____22990, branch_guard,
                                                effect_label, cflags,
                                                maybe_return_c, uu____23007,
                                                erasable)))))))))))
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
          let uu____23051 = check_let_bound_def true env1 lb in
          (match uu____23051 with
           | (e1, univ_vars, c1, g1, annotated) ->
               let uu____23073 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____23094 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____23094, univ_vars, c1)
                 else
                   (let g11 =
                      let uu____23099 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____23099
                        (FStar_TypeChecker_Rel.resolve_implicits env1) in
                    let uu____23100 = FStar_TypeChecker_Common.lcomp_comp c1 in
                    match uu____23100 with
                    | (comp1, g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1 in
                        let uu____23118 =
                          let uu____23131 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)] in
                          FStar_List.hd uu____23131 in
                        (match uu____23118 with
                         | (uu____23180, univs, e11, c11, gvs) ->
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
                             let uu____23194 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11 in
                             (g14, e11, univs, uu____23194))) in
               (match uu____23073 with
                | (g11, e11, univ_vars1, c11) ->
                    let uu____23211 =
                      let uu____23220 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____23220
                      then
                        let uu____23229 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____23229 with
                        | (ok, c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____23258 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.log_issue uu____23258
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____23259 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____23259, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____23270 =
                            FStar_TypeChecker_Common.lcomp_comp c11 in
                          match uu____23270 with
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
                                  let uu____23294 =
                                    FStar_Syntax_Util.is_pure_comp c in
                                  if uu____23294
                                  then e2
                                  else
                                    ((let uu____23299 =
                                        FStar_TypeChecker_Env.get_range env1 in
                                      FStar_Errors.log_issue uu____23299
                                        FStar_TypeChecker_Err.top_level_effect);
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Masked_effect)))
                                       e2.FStar_Syntax_Syntax.pos) in
                                (e21, c))))) in
                    (match uu____23211 with
                     | (e21, c12) ->
                         ((let uu____23323 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium in
                           if uu____23323
                           then
                             let uu____23324 =
                               FStar_Syntax_Print.term_to_string e11 in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____23324
                           else ());
                          (let e12 =
                             let uu____23327 = FStar_Options.tcnorm () in
                             if uu____23327
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
                           (let uu____23330 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium in
                            if uu____23330
                            then
                              let uu____23331 =
                                FStar_Syntax_Print.term_to_string e12 in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____23331
                            else ());
                           (let cres =
                              let uu____23334 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12 in
                              if uu____23334
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
                                   | (wp, uu____23339)::[] -> wp
                                   | uu____23364 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args" in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name in
                                 let wp2 =
                                   let ret =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_return_vc_combinator in
                                   let uu____23378 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [FStar_Syntax_Syntax.U_zero] env1
                                       c1_eff_decl ret in
                                   let uu____23379 =
                                     let uu____23380 =
                                       FStar_Syntax_Syntax.as_arg
                                         FStar_Syntax_Syntax.t_unit in
                                     let uu____23389 =
                                       let uu____23400 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.unit_const in
                                       [uu____23400] in
                                     uu____23380 :: uu____23389 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____23378
                                     uu____23379 e21.FStar_Syntax_Syntax.pos in
                                 let wp =
                                   let bind =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator in
                                   let uu____23435 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       (FStar_List.append
                                          c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                          [FStar_Syntax_Syntax.U_zero]) env1
                                       c1_eff_decl bind in
                                   let uu____23436 =
                                     let uu____23437 =
                                       let uu____23446 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_constant
                                              (FStar_Const.Const_range
                                                 (lb.FStar_Syntax_Syntax.lbpos)))
                                           lb.FStar_Syntax_Syntax.lbpos in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____23446 in
                                     let uu____23455 =
                                       let uu____23466 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           c1_comp_typ.FStar_Syntax_Syntax.result_typ in
                                       let uu____23483 =
                                         let uu____23494 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.t_unit in
                                         let uu____23503 =
                                           let uu____23514 =
                                             FStar_Syntax_Syntax.as_arg c1_wp in
                                           let uu____23523 =
                                             let uu____23534 =
                                               let uu____23543 =
                                                 let uu____23544 =
                                                   let uu____23545 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       c1_comp_typ.FStar_Syntax_Syntax.result_typ in
                                                   [uu____23545] in
                                                 FStar_Syntax_Util.abs
                                                   uu____23544 wp2
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Util.mk_residual_comp
                                                         FStar_Parser_Const.effect_Tot_lid
                                                         FStar_Pervasives_Native.None
                                                         [FStar_Syntax_Syntax.TOTAL])) in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23543 in
                                             [uu____23534] in
                                           uu____23514 :: uu____23523 in
                                         uu____23494 :: uu____23503 in
                                       uu____23466 :: uu____23483 in
                                     uu____23437 :: uu____23455 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____23435
                                     uu____23436 lb.FStar_Syntax_Syntax.lbpos in
                                 let uu____23622 =
                                   let uu____23623 =
                                     let uu____23634 =
                                       FStar_Syntax_Syntax.as_arg wp in
                                     [uu____23634] in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____23623;
                                     FStar_Syntax_Syntax.flags = []
                                   } in
                                 FStar_Syntax_Syntax.mk_Comp uu____23622) in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars1
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos in
                            let uu____23662 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                e.FStar_Syntax_Syntax.pos in
                            let uu____23673 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres in
                            (uu____23662, uu____23673,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____23674 -> failwith "Impossible"
and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lem_typ ->
      fun c2 ->
        let uu____23684 = FStar_Syntax_Util.is_smt_lemma lem_typ in
        if uu____23684
        then
          let universe_of_binders bs =
            let uu____23709 =
              FStar_List.fold_left
                (fun uu____23734 ->
                   fun b ->
                     match uu____23734 with
                     | (env1, us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b] in
                         (env2, (u :: us))) (env, []) bs in
            match uu____23709 with | (uu____23782, us) -> FStar_List.rev us in
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
            let uu___3222_23814 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3222_23814.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3222_23814.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3222_23814.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3222_23814.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3222_23814.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3222_23814.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3222_23814.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3222_23814.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3222_23814.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3222_23814.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3222_23814.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3222_23814.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3222_23814.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3222_23814.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3222_23814.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3222_23814.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___3222_23814.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___3222_23814.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3222_23814.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3222_23814.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3222_23814.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3222_23814.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3222_23814.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3222_23814.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3222_23814.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3222_23814.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3222_23814.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3222_23814.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3222_23814.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3222_23814.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3222_23814.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3222_23814.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3222_23814.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3222_23814.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3222_23814.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3222_23814.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3222_23814.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3222_23814.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3222_23814.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3222_23814.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3222_23814.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3222_23814.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3222_23814.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3222_23814.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3222_23814.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___3222_23814.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let uu____23815 =
            let uu____23826 =
              let uu____23827 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____23827 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____23826 lb in
          (match uu____23815 with
           | (e1, uu____23849, c1, g1, annotated) ->
               let pure_or_ghost =
                 FStar_TypeChecker_Common.is_pure_or_ghost_lcomp c1 in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____23858 =
                     let uu____23863 =
                       let uu____23864 = FStar_Syntax_Print.term_to_string e1 in
                       let uu____23865 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____23864 uu____23865 in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____23863) in
                   FStar_Errors.raise_error uu____23858
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____23872 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ) in
                   if uu____23872
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs in
                 let x =
                   let uu___3237_23881 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3237_23881.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3237_23881.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   } in
                 let uu____23882 =
                   let uu____23887 =
                     let uu____23888 = FStar_Syntax_Syntax.mk_binder x in
                     [uu____23888] in
                   FStar_Syntax_Subst.open_term uu____23887 e2 in
                 match uu____23882 with
                 | (xb, e21) ->
                     let xbinder = FStar_List.hd xb in
                     let x1 = FStar_Pervasives_Native.fst xbinder in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1 in
                     let uu____23932 =
                       let uu____23939 = tc_term env_x e21 in
                       FStar_All.pipe_right uu____23939
                         (fun uu____23965 ->
                            match uu____23965 with
                            | (e22, c2, g2) ->
                                let uu____23981 =
                                  let uu____23986 =
                                    FStar_All.pipe_right
                                      (fun uu____24001 ->
                                         "folding guard g2 of e2 in the lcomp")
                                      (fun uu____24005 ->
                                         FStar_Pervasives_Native.Some
                                           uu____24005) in
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    uu____23986 env_x e22 c2 g2 in
                                (match uu____23981 with
                                 | (c21, g21) -> (e22, c21, g21))) in
                     (match uu____23932 with
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
                            let uu____24033 =
                              let uu____24034 =
                                let uu____24047 =
                                  FStar_Syntax_Subst.close xb e23 in
                                ((false, [lb1]), uu____24047) in
                              FStar_Syntax_Syntax.Tm_let uu____24034 in
                            FStar_Syntax_Syntax.mk uu____24033
                              e.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ in
                          let g21 =
                            let uu____24062 =
                              let uu____24063 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2) in
                              FStar_All.pipe_right uu____24063
                                (FStar_TypeChecker_Env.is_layered_effect env2) in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____24062 xb g2 in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g21 in
                          let uu____24065 =
                            let uu____24066 =
                              FStar_TypeChecker_Env.expected_typ env2 in
                            FStar_Option.isSome uu____24066 in
                          if uu____24065
                          then
                            let tt =
                              let uu____24076 =
                                FStar_TypeChecker_Env.expected_typ env2 in
                              FStar_All.pipe_right uu____24076
                                FStar_Option.get in
                            ((let uu____24082 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports") in
                              if uu____24082
                              then
                                let uu____24083 =
                                  FStar_Syntax_Print.term_to_string tt in
                                let uu____24084 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____24083 uu____24084
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____24087 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ in
                             match uu____24087 with
                             | (t, g_ex) ->
                                 ((let uu____24101 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports") in
                                   if uu____24101
                                   then
                                     let uu____24102 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ in
                                     let uu____24103 =
                                       FStar_Syntax_Print.term_to_string t in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____24102 uu____24103
                                   else ());
                                  (let uu____24105 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard in
                                   (e4,
                                     (let uu___3276_24107 = cres in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3276_24107.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3276_24107.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3276_24107.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____24105))))))))
      | uu____24108 ->
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
          let uu____24140 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____24140 with
           | (lbs1, e21) ->
               let uu____24159 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____24159 with
                | (env0, topt) ->
                    let uu____24178 = build_let_rec_env true env0 lbs1 in
                    (match uu____24178 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____24200 = check_let_recs rec_env lbs2 in
                         (match uu____24200 with
                          | (lbs3, g_lbs) ->
                              let g_lbs1 =
                                let uu____24220 =
                                  let uu____24221 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs in
                                  FStar_All.pipe_right uu____24221
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1) in
                                FStar_All.pipe_right uu____24220
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1) in
                              let all_lb_names =
                                let uu____24227 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____24227
                                  (fun uu____24244 ->
                                     FStar_Pervasives_Native.Some uu____24244) in
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
                                     let uu____24277 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb ->
                                               let uu____24311 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____24311))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____24277 in
                                   FStar_List.map2
                                     (fun uu____24345 ->
                                        fun lb ->
                                          match uu____24345 with
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
                                let uu____24393 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____24393 in
                              let uu____24394 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____24394 with
                               | (lbs5, e22) ->
                                   ((let uu____24414 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____24414
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____24415 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____24415, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____24426 -> failwith "Impossible"
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
          let uu____24458 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____24458 with
           | (lbs1, e21) ->
               let uu____24477 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____24477 with
                | (env0, topt) ->
                    let uu____24496 = build_let_rec_env false env0 lbs1 in
                    (match uu____24496 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____24518 =
                           let uu____24525 = check_let_recs rec_env lbs2 in
                           FStar_All.pipe_right uu____24525
                             (fun uu____24548 ->
                                match uu____24548 with
                                | (lbs3, g) ->
                                    let uu____24567 =
                                      FStar_TypeChecker_Env.conj_guard g_t g in
                                    (lbs3, uu____24567)) in
                         (match uu____24518 with
                          | (lbs3, g_lbs) ->
                              let uu____24582 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2 ->
                                        fun lb ->
                                          let x =
                                            let uu___3351_24605 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3351_24605.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3351_24605.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___3354_24607 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3354_24607.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3354_24607.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3354_24607.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3354_24607.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3354_24607.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3354_24607.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____24582 with
                               | (env2, lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____24634 = tc_term env2 e21 in
                                   (match uu____24634 with
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
                                          let uu____24658 =
                                            let uu____24659 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____24659 g2 in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____24658 in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_wp_lcomp
                                            env2 bvs cres3 in
                                        let tres =
                                          norm env2
                                            cres4.FStar_TypeChecker_Common.res_typ in
                                        let cres5 =
                                          let uu___3375_24669 = cres4 in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3375_24669.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3375_24669.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3375_24669.FStar_TypeChecker_Common.comp_thunk)
                                          } in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb ->
                                                    let uu____24677 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____24677)) in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard in
                                        let uu____24678 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____24678 with
                                         | (lbs5, e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____24716 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  let uu____24717 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  (match uu____24717 with
                                                   | (tres1, g_ex) ->
                                                       let cres6 =
                                                         let uu___3391_24731
                                                           = cres5 in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3391_24731.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3391_24731.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3391_24731.FStar_TypeChecker_Common.comp_thunk)
                                                         } in
                                                       let uu____24732 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1 in
                                                       (e, cres6,
                                                         uu____24732))))))))))
      | uu____24733 -> failwith "Impossible"
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
          let uu____24782 = FStar_Options.ml_ish () in
          if uu____24782
          then FStar_Pervasives_Native.None
          else
            (let lbtyp0 = lbtyp in
             let uu____24795 = FStar_Syntax_Util.abs_formals lbdef in
             match uu____24795 with
             | (actuals, body, body_lc) ->
                 let actuals1 =
                   let uu____24818 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____24818 actuals in
                 let nactuals = FStar_List.length actuals1 in
                 let uu____24826 =
                   FStar_TypeChecker_Normalize.get_n_binders env nactuals
                     lbtyp in
                 (match uu____24826 with
                  | (formals, c) ->
                      (if
                         (FStar_List.isEmpty formals) ||
                           (FStar_List.isEmpty actuals1)
                       then
                         (let uu____24852 =
                            let uu____24857 =
                              let uu____24858 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              let uu____24859 =
                                FStar_Syntax_Print.term_to_string lbtyp in
                              FStar_Util.format2
                                "Only function literals with arrow types can be defined recursively; got %s : %s"
                                uu____24858 uu____24859 in
                            (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                              uu____24857) in
                          FStar_Errors.raise_error uu____24852
                            lbtyp.FStar_Syntax_Syntax.pos)
                       else ();
                       (let nformals = FStar_List.length formals in
                        let uu____24862 =
                          let uu____24863 =
                            FStar_All.pipe_right
                              (FStar_Syntax_Util.comp_effect_name c)
                              (FStar_TypeChecker_Env.lookup_effect_quals env) in
                          FStar_All.pipe_right uu____24863
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect) in
                        if uu____24862
                        then
                          let uu____24876 =
                            let uu____24881 =
                              FStar_Syntax_Util.abs actuals1 body body_lc in
                            (nformals, uu____24881) in
                          FStar_Pervasives_Native.Some uu____24876
                        else FStar_Pervasives_Native.None)))) in
        let uu____24891 =
          FStar_List.fold_left
            (fun uu____24925 ->
               fun lb ->
                 match uu____24925 with
                 | (lbs1, env1, g_acc) ->
                     let uu____24950 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____24950 with
                      | (univ_vars, t, check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let uu____24970 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars in
                               let uu____24987 =
                                 let uu____24994 =
                                   let uu____24995 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____24995 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3431_25006 = env01 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3431_25006.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3431_25006.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3431_25006.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3431_25006.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3431_25006.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3431_25006.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3431_25006.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3431_25006.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3431_25006.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3431_25006.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3431_25006.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3431_25006.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3431_25006.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3431_25006.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3431_25006.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3431_25006.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___3431_25006.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3431_25006.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3431_25006.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3431_25006.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3431_25006.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3431_25006.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3431_25006.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3431_25006.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3431_25006.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3431_25006.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3431_25006.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3431_25006.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3431_25006.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3431_25006.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3431_25006.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3431_25006.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3431_25006.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3431_25006.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3431_25006.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3431_25006.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3431_25006.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3431_25006.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3431_25006.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3431_25006.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3431_25006.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3431_25006.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3431_25006.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3431_25006.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3431_25006.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___3431_25006.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }) t uu____24994 "" in
                               match uu____24987 with
                               | (t1, uu____25014, g) ->
                                   let uu____25016 =
                                     let uu____25017 =
                                       let uu____25018 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2) in
                                       FStar_All.pipe_right uu____25018
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2) in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____25017 in
                                   let uu____25019 = norm env01 t1 in
                                   (uu____25016, uu____25019)) in
                          (match uu____24970 with
                           | (g, t1) ->
                               let uu____25038 =
                                 let uu____25043 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1 in
                                 match uu____25043 with
                                 | FStar_Pervasives_Native.Some (arity, def)
                                     ->
                                     let lb1 =
                                       let uu___3444_25061 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3444_25061.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3444_25061.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = def;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3444_25061.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3444_25061.FStar_Syntax_Syntax.lbpos)
                                       } in
                                     let env3 =
                                       let uu___3447_25063 = env2 in
                                       {
                                         FStar_TypeChecker_Env.solver =
                                           (uu___3447_25063.FStar_TypeChecker_Env.solver);
                                         FStar_TypeChecker_Env.range =
                                           (uu___3447_25063.FStar_TypeChecker_Env.range);
                                         FStar_TypeChecker_Env.curmodule =
                                           (uu___3447_25063.FStar_TypeChecker_Env.curmodule);
                                         FStar_TypeChecker_Env.gamma =
                                           (uu___3447_25063.FStar_TypeChecker_Env.gamma);
                                         FStar_TypeChecker_Env.gamma_sig =
                                           (uu___3447_25063.FStar_TypeChecker_Env.gamma_sig);
                                         FStar_TypeChecker_Env.gamma_cache =
                                           (uu___3447_25063.FStar_TypeChecker_Env.gamma_cache);
                                         FStar_TypeChecker_Env.modules =
                                           (uu___3447_25063.FStar_TypeChecker_Env.modules);
                                         FStar_TypeChecker_Env.expected_typ =
                                           (uu___3447_25063.FStar_TypeChecker_Env.expected_typ);
                                         FStar_TypeChecker_Env.sigtab =
                                           (uu___3447_25063.FStar_TypeChecker_Env.sigtab);
                                         FStar_TypeChecker_Env.attrtab =
                                           (uu___3447_25063.FStar_TypeChecker_Env.attrtab);
                                         FStar_TypeChecker_Env.instantiate_imp
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.instantiate_imp);
                                         FStar_TypeChecker_Env.effects =
                                           (uu___3447_25063.FStar_TypeChecker_Env.effects);
                                         FStar_TypeChecker_Env.generalize =
                                           (uu___3447_25063.FStar_TypeChecker_Env.generalize);
                                         FStar_TypeChecker_Env.letrecs =
                                           (((lb1.FStar_Syntax_Syntax.lbname),
                                              arity, t1, univ_vars) ::
                                           (env2.FStar_TypeChecker_Env.letrecs));
                                         FStar_TypeChecker_Env.top_level =
                                           (uu___3447_25063.FStar_TypeChecker_Env.top_level);
                                         FStar_TypeChecker_Env.check_uvars =
                                           (uu___3447_25063.FStar_TypeChecker_Env.check_uvars);
                                         FStar_TypeChecker_Env.use_eq =
                                           (uu___3447_25063.FStar_TypeChecker_Env.use_eq);
                                         FStar_TypeChecker_Env.use_eq_strict
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.use_eq_strict);
                                         FStar_TypeChecker_Env.is_iface =
                                           (uu___3447_25063.FStar_TypeChecker_Env.is_iface);
                                         FStar_TypeChecker_Env.admit =
                                           (uu___3447_25063.FStar_TypeChecker_Env.admit);
                                         FStar_TypeChecker_Env.lax =
                                           (uu___3447_25063.FStar_TypeChecker_Env.lax);
                                         FStar_TypeChecker_Env.lax_universes
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.lax_universes);
                                         FStar_TypeChecker_Env.phase1 =
                                           (uu___3447_25063.FStar_TypeChecker_Env.phase1);
                                         FStar_TypeChecker_Env.failhard =
                                           (uu___3447_25063.FStar_TypeChecker_Env.failhard);
                                         FStar_TypeChecker_Env.nosynth =
                                           (uu___3447_25063.FStar_TypeChecker_Env.nosynth);
                                         FStar_TypeChecker_Env.uvar_subtyping
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.uvar_subtyping);
                                         FStar_TypeChecker_Env.tc_term =
                                           (uu___3447_25063.FStar_TypeChecker_Env.tc_term);
                                         FStar_TypeChecker_Env.type_of =
                                           (uu___3447_25063.FStar_TypeChecker_Env.type_of);
                                         FStar_TypeChecker_Env.universe_of =
                                           (uu___3447_25063.FStar_TypeChecker_Env.universe_of);
                                         FStar_TypeChecker_Env.check_type_of
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.check_type_of);
                                         FStar_TypeChecker_Env.use_bv_sorts =
                                           (uu___3447_25063.FStar_TypeChecker_Env.use_bv_sorts);
                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.qtbl_name_and_index);
                                         FStar_TypeChecker_Env.normalized_eff_names
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.normalized_eff_names);
                                         FStar_TypeChecker_Env.fv_delta_depths
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.fv_delta_depths);
                                         FStar_TypeChecker_Env.proof_ns =
                                           (uu___3447_25063.FStar_TypeChecker_Env.proof_ns);
                                         FStar_TypeChecker_Env.synth_hook =
                                           (uu___3447_25063.FStar_TypeChecker_Env.synth_hook);
                                         FStar_TypeChecker_Env.try_solve_implicits_hook
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                         FStar_TypeChecker_Env.splice =
                                           (uu___3447_25063.FStar_TypeChecker_Env.splice);
                                         FStar_TypeChecker_Env.mpreprocess =
                                           (uu___3447_25063.FStar_TypeChecker_Env.mpreprocess);
                                         FStar_TypeChecker_Env.postprocess =
                                           (uu___3447_25063.FStar_TypeChecker_Env.postprocess);
                                         FStar_TypeChecker_Env.identifier_info
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.identifier_info);
                                         FStar_TypeChecker_Env.tc_hooks =
                                           (uu___3447_25063.FStar_TypeChecker_Env.tc_hooks);
                                         FStar_TypeChecker_Env.dsenv =
                                           (uu___3447_25063.FStar_TypeChecker_Env.dsenv);
                                         FStar_TypeChecker_Env.nbe =
                                           (uu___3447_25063.FStar_TypeChecker_Env.nbe);
                                         FStar_TypeChecker_Env.strict_args_tab
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.strict_args_tab);
                                         FStar_TypeChecker_Env.erasable_types_tab
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.erasable_types_tab);
                                         FStar_TypeChecker_Env.enable_defer_to_tac
                                           =
                                           (uu___3447_25063.FStar_TypeChecker_Env.enable_defer_to_tac)
                                       } in
                                     (lb1, env3)
                                 | FStar_Pervasives_Native.None ->
                                     let lb1 =
                                       let uu___3451_25077 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3451_25077.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3451_25077.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3451_25077.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3451_25077.FStar_Syntax_Syntax.lbpos)
                                       } in
                                     let uu____25078 =
                                       FStar_TypeChecker_Env.push_let_binding
                                         env2 lb1.FStar_Syntax_Syntax.lbname
                                         (univ_vars, t1) in
                                     (lb1, uu____25078) in
                               (match uu____25038 with
                                | (lb1, env3) -> ((lb1 :: lbs1), env3, g)))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs in
        match uu____24891 with
        | (lbs1, env1, g) -> ((FStar_List.rev lbs1), env1, g)
and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun lbs ->
      let uu____25118 =
        let uu____25127 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb ->
                  let uu____25153 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____25153 with
                  | (bs, t, lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____25183 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____25183
                       | uu____25188 ->
                           let arity =
                             let uu____25191 =
                               FStar_TypeChecker_Env.get_letrec_arity env
                                 lb.FStar_Syntax_Syntax.lbname in
                             match uu____25191 with
                             | FStar_Pervasives_Native.Some n -> n
                             | FStar_Pervasives_Native.None ->
                                 FStar_List.length bs in
                           let uu____25201 = FStar_List.splitAt arity bs in
                           (match uu____25201 with
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
                                  let uu___3483_25296 = lb in
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      (uu___3483_25296.FStar_Syntax_Syntax.lbname);
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___3483_25296.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp =
                                      (uu___3483_25296.FStar_Syntax_Syntax.lbtyp);
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___3483_25296.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___3483_25296.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___3483_25296.FStar_Syntax_Syntax.lbpos)
                                  } in
                                let uu____25297 =
                                  let uu____25304 =
                                    FStar_TypeChecker_Env.set_expected_typ
                                      env lb1.FStar_Syntax_Syntax.lbtyp in
                                  tc_tot_or_gtot_term uu____25304
                                    lb1.FStar_Syntax_Syntax.lbdef in
                                (match uu____25297 with
                                 | (e, c, g) ->
                                     ((let uu____25313 =
                                         let uu____25314 =
                                           FStar_TypeChecker_Common.is_total_lcomp
                                             c in
                                         Prims.op_Negation uu____25314 in
                                       if uu____25313
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
        FStar_All.pipe_right uu____25127 FStar_List.unzip in
      match uu____25118 with
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
        let uu____25363 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____25363 with
        | (env1, uu____25381) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____25389 = check_lbtyp top_level env lb in
            (match uu____25389 with
             | (topt, wf_annot, univ_vars, univ_opening, env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____25433 =
                     tc_maybe_toplevel_term
                       (let uu___3514_25442 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3514_25442.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3514_25442.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3514_25442.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3514_25442.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3514_25442.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3514_25442.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3514_25442.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3514_25442.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3514_25442.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3514_25442.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3514_25442.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3514_25442.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3514_25442.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3514_25442.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3514_25442.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3514_25442.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___3514_25442.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3514_25442.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3514_25442.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3514_25442.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3514_25442.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3514_25442.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3514_25442.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3514_25442.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3514_25442.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3514_25442.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3514_25442.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3514_25442.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3514_25442.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3514_25442.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3514_25442.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3514_25442.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3514_25442.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3514_25442.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3514_25442.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3514_25442.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3514_25442.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3514_25442.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3514_25442.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3514_25442.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3514_25442.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3514_25442.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3514_25442.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3514_25442.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3514_25442.FStar_TypeChecker_Env.erasable_types_tab);
                          FStar_TypeChecker_Env.enable_defer_to_tac =
                            (uu___3514_25442.FStar_TypeChecker_Env.enable_defer_to_tac)
                        }) e11 in
                   match uu____25433 with
                   | (e12, c1, g1) ->
                       let uu____25456 =
                         let uu____25461 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____25466 ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____25461 e12 c1 wf_annot in
                       (match uu____25456 with
                        | (c11, guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f in
                            ((let uu____25481 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____25481
                              then
                                let uu____25482 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____25483 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11 in
                                let uu____25484 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____25482 uu____25483 uu____25484
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
            let uu____25518 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____25518 with
             | (univ_opening, univ_vars) ->
                 let uu____25551 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars,
                   univ_opening, uu____25551))
        | uu____25556 ->
            let uu____25557 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____25557 with
             | (univ_opening, univ_vars) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____25606 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars,
                     univ_opening, uu____25606)
                 else
                   (let uu____25612 = FStar_Syntax_Util.type_u () in
                    match uu____25612 with
                    | (k, uu____25632) ->
                        let uu____25633 =
                          tc_check_tot_or_gtot_term env1 t1 k "" in
                        (match uu____25633 with
                         | (t2, uu____25655, g) ->
                             ((let uu____25658 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____25658
                               then
                                 let uu____25659 =
                                   let uu____25660 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____25660 in
                                 let uu____25661 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____25659 uu____25661
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____25664 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars, univ_opening, uu____25664))))))
and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env ->
    fun uu____25670 ->
      match uu____25670 with
      | (x, imp) ->
          let uu____25697 = FStar_Syntax_Util.type_u () in
          (match uu____25697 with
           | (tu, u) ->
               ((let uu____25719 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____25719
                 then
                   let uu____25720 = FStar_Syntax_Print.bv_to_string x in
                   let uu____25721 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____25722 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____25720 uu____25721 uu____25722
                 else ());
                (let uu____25724 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu "" in
                 match uu____25724 with
                 | (t, uu____25746, g) ->
                     let uu____25748 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau_or_attr) ->
                           (match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let uu____25771 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau in
                                (match uu____25771 with
                                 | (tau1, uu____25785, g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                               tau1))), g1))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let uu____25792 =
                                  tc_check_tot_or_gtot_term env attr
                                    FStar_Syntax_Syntax.t_unit "" in
                                (match uu____25792 with
                                 | (attr1, uu____25806, g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                               attr1))),
                                       FStar_TypeChecker_Env.trivial_guard)))
                       | uu____25810 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard) in
                     (match uu____25748 with
                      | (imp1, g') ->
                          let x1 =
                            ((let uu___3584_25845 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3584_25845.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3584_25845.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1) in
                          ((let uu____25847 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High in
                            if uu____25847
                            then
                              let uu____25848 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1) in
                              let uu____25851 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____25848
                                uu____25851
                            else ());
                           (let uu____25853 = push_binding env x1 in
                            (x1, uu____25853, g, u)))))))
and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env ->
    fun bs ->
      (let uu____25865 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
       if uu____25865
       then
         let uu____25866 = FStar_Syntax_Print.binders_to_string ", " bs in
         FStar_Util.print1 "Checking binders %s\n" uu____25866
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____25975 = tc_binder env1 b in
             (match uu____25975 with
              | (b1, env', g, u) ->
                  let uu____26024 = aux env' bs2 in
                  (match uu____26024 with
                   | (bs3, env'1, g', us) ->
                       let uu____26085 =
                         let uu____26086 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g' in
                         FStar_TypeChecker_Env.conj_guard g uu____26086 in
                       ((b1 :: bs3), env'1, uu____26085, (u :: us)))) in
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
          (fun uu____26194 ->
             fun uu____26195 ->
               match (uu____26194, uu____26195) with
               | ((t, imp), (args1, g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____26287 = tc_term en1 t in
                     match uu____26287 with
                     | (t1, uu____26307, g') ->
                         let uu____26309 =
                           FStar_TypeChecker_Env.conj_guard g g' in
                         (((t1, imp) :: args1), uu____26309)))) args
          ([], FStar_TypeChecker_Env.trivial_guard) in
      FStar_List.fold_right
        (fun p ->
           fun uu____26363 ->
             match uu____26363 with
             | (pats1, g) ->
                 let uu____26390 = tc_args en p in
                 (match uu____26390 with
                  | (args, g') ->
                      let uu____26403 = FStar_TypeChecker_Env.conj_guard g g' in
                      ((args :: pats1), uu____26403))) pats
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
        let uu____26417 = tc_maybe_toplevel_term env e in
        match uu____26417 with
        | (e1, c, g) ->
            let uu____26433 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c in
            if uu____26433
            then (e1, c, g)
            else
              (let g1 =
                 FStar_TypeChecker_Rel.solve_deferred_constraints env g in
               let uu____26442 = FStar_TypeChecker_Common.lcomp_comp c in
               match uu____26442 with
               | (c1, g_c) ->
                   let c2 = norm_c env c1 in
                   let uu____26456 =
                     let uu____26461 =
                       FStar_TypeChecker_Util.is_pure_effect env
                         (FStar_Syntax_Util.comp_effect_name c2) in
                     if uu____26461
                     then
                       let uu____26466 =
                         FStar_Syntax_Syntax.mk_Total
                           (FStar_Syntax_Util.comp_result c2) in
                       (uu____26466, false)
                     else
                       (let uu____26468 =
                          FStar_Syntax_Syntax.mk_GTotal
                            (FStar_Syntax_Util.comp_result c2) in
                        (uu____26468, true)) in
                   (match uu____26456 with
                    | (target_comp, allow_ghost) ->
                        let uu____26477 =
                          FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                        (match uu____26477 with
                         | FStar_Pervasives_Native.Some g' ->
                             let uu____26487 =
                               FStar_TypeChecker_Common.lcomp_of_comp
                                 target_comp in
                             let uu____26488 =
                               let uu____26489 =
                                 FStar_TypeChecker_Env.conj_guard g_c g' in
                               FStar_TypeChecker_Env.conj_guard g1
                                 uu____26489 in
                             (e1, uu____26487, uu____26488)
                         | uu____26490 ->
                             if allow_ghost
                             then
                               let uu____26499 =
                                 FStar_TypeChecker_Err.expected_ghost_expression
                                   e1 c2 msg in
                               FStar_Errors.raise_error uu____26499
                                 e1.FStar_Syntax_Syntax.pos
                             else
                               (let uu____26511 =
                                  FStar_TypeChecker_Err.expected_pure_expression
                                    e1 c2 msg in
                                FStar_Errors.raise_error uu____26511
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
      let uu____26537 = tc_tot_or_gtot_term env t in
      match uu____26537 with
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
        let uu____26567 = tc_check_tot_or_gtot_term env t k "" in
        match uu____26567 with
        | (t1, uu____26575, g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      (let uu____26595 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____26595
       then
         let uu____26596 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____26596
       else ());
      (let env1 =
         let uu___3680_26599 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3680_26599.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3680_26599.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3680_26599.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3680_26599.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3680_26599.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3680_26599.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3680_26599.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3680_26599.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3680_26599.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3680_26599.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3680_26599.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3680_26599.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3680_26599.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3680_26599.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3680_26599.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___3680_26599.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___3680_26599.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3680_26599.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3680_26599.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3680_26599.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3680_26599.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3680_26599.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3680_26599.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3680_26599.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3680_26599.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3680_26599.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3680_26599.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3680_26599.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3680_26599.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3680_26599.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3680_26599.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3680_26599.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3680_26599.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3680_26599.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3680_26599.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3680_26599.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3680_26599.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3680_26599.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3680_26599.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3680_26599.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3680_26599.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3680_26599.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3680_26599.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3680_26599.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___3680_26599.FStar_TypeChecker_Env.enable_defer_to_tac)
         } in
       let uu____26608 =
         try
           (fun uu___3684_26622 ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1, msg, uu____26643) ->
             let uu____26644 = FStar_TypeChecker_Env.get_range env1 in
             FStar_Errors.raise_error (e1, msg) uu____26644 in
       match uu____26608 with
       | (t, c, g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c in
           let uu____26661 = FStar_TypeChecker_Common.is_total_lcomp c1 in
           if uu____26661
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____26669 =
                let uu____26674 =
                  let uu____26675 = FStar_Syntax_Print.term_to_string e in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____26675 in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____26674) in
              let uu____26676 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____26669 uu____26676))
let level_of_type_fail :
  'uuuuuu26691 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'uuuuuu26691
  =
  fun env ->
    fun e ->
      fun t ->
        let uu____26707 =
          let uu____26712 =
            let uu____26713 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____26713 t in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____26712) in
        let uu____26714 = FStar_TypeChecker_Env.get_range env in
        FStar_Errors.raise_error uu____26707 uu____26714
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      fun t ->
        let rec aux retry t1 =
          let uu____26745 =
            let uu____26746 = FStar_Syntax_Util.unrefine t1 in
            uu____26746.FStar_Syntax_Syntax.n in
          match uu____26745 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____26750 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1 in
                aux false t2
              else
                (let uu____26753 = FStar_Syntax_Util.type_u () in
                 match uu____26753 with
                 | (t_u, u) ->
                     let env1 =
                       let uu___3716_26761 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3716_26761.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3716_26761.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3716_26761.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3716_26761.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3716_26761.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3716_26761.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3716_26761.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3716_26761.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3716_26761.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3716_26761.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3716_26761.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3716_26761.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3716_26761.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3716_26761.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3716_26761.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3716_26761.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3716_26761.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3716_26761.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3716_26761.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3716_26761.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3716_26761.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3716_26761.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3716_26761.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3716_26761.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3716_26761.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3716_26761.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3716_26761.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3716_26761.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3716_26761.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3716_26761.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3716_26761.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3716_26761.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3716_26761.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3716_26761.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3716_26761.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3716_26761.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3716_26761.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3716_26761.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3716_26761.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3716_26761.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3716_26761.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3716_26761.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3716_26761.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3716_26761.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3716_26761.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3716_26761.FStar_TypeChecker_Env.enable_defer_to_tac)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____26765 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____26765
                       | uu____26766 ->
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
      let uu____26781 =
        let uu____26782 = FStar_Syntax_Subst.compress e in
        uu____26782.FStar_Syntax_Syntax.n in
      match uu____26781 with
      | FStar_Syntax_Syntax.Tm_bvar uu____26785 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____26786 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____26801 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs, t, uu____26817) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t, uu____26861) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____26868 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____26868 with | ((uu____26877, t), uu____26879) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____26885 = FStar_Syntax_Util.unfold_lazy i in
          universe_of_aux env uu____26885
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____26888, (FStar_Util.Inl t, uu____26890), uu____26891) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____26938, (FStar_Util.Inr c, uu____26940), uu____26941) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____26989 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____26998;
             FStar_Syntax_Syntax.vars = uu____26999;_},
           us)
          ->
          let uu____27005 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____27005 with
           | ((us', t), uu____27016) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____27022 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____27022)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____27040 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____27041 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x, uu____27049) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____27076 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____27076 with
           | (bs1, c1) ->
               let us =
                 FStar_List.map
                   (fun uu____27096 ->
                      match uu____27096 with
                      | (b, uu____27104) ->
                          let uu____27109 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____27109) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____27114 = universe_of_aux env res in
                 level_of_type env res uu____27114 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____27222 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____27237 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____27266 ->
                let uu____27267 = universe_of_aux env hd2 in
                (uu____27267, args1)
            | FStar_Syntax_Syntax.Tm_name uu____27278 ->
                let uu____27279 = universe_of_aux env hd2 in
                (uu____27279, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____27290 ->
                let uu____27303 = universe_of_aux env hd2 in
                (uu____27303, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____27314 ->
                let uu____27321 = universe_of_aux env hd2 in
                (uu____27321, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____27332 ->
                let uu____27359 = universe_of_aux env hd2 in
                (uu____27359, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____27370 ->
                let uu____27377 = universe_of_aux env hd2 in
                (uu____27377, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____27388 ->
                let uu____27389 = universe_of_aux env hd2 in
                (uu____27389, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____27400 ->
                let uu____27415 = universe_of_aux env hd2 in
                (uu____27415, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____27426 ->
                let uu____27433 = universe_of_aux env hd2 in
                (uu____27433, args1)
            | FStar_Syntax_Syntax.Tm_type uu____27444 ->
                let uu____27445 = universe_of_aux env hd2 in
                (uu____27445, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____27456, hd3::uu____27458) ->
                let uu____27523 = FStar_Syntax_Subst.open_branch hd3 in
                (match uu____27523 with
                 | (uu____27538, uu____27539, hd4) ->
                     let uu____27557 = FStar_Syntax_Util.head_and_args hd4 in
                     (match uu____27557 with
                      | (hd5, args') ->
                          type_of_head retry hd5
                            (FStar_List.append args' args1)))
            | uu____27622 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e in
                let uu____27624 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____27624 with
                 | (hd3, args2) -> type_of_head false hd3 args2)
            | uu____27681 ->
                let uu____27682 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____27682 with
                 | (env1, uu____27704) ->
                     let env2 =
                       let uu___3877_27710 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3877_27710.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3877_27710.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3877_27710.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3877_27710.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3877_27710.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3877_27710.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3877_27710.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3877_27710.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3877_27710.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3877_27710.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3877_27710.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3877_27710.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3877_27710.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3877_27710.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3877_27710.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3877_27710.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3877_27710.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3877_27710.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3877_27710.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3877_27710.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3877_27710.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3877_27710.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3877_27710.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3877_27710.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3877_27710.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3877_27710.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3877_27710.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3877_27710.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3877_27710.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3877_27710.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3877_27710.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3877_27710.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3877_27710.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3877_27710.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3877_27710.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3877_27710.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3877_27710.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3877_27710.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3877_27710.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3877_27710.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3877_27710.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3877_27710.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3877_27710.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3877_27710.FStar_TypeChecker_Env.enable_defer_to_tac)
                       } in
                     ((let uu____27712 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____27712
                       then
                         let uu____27713 =
                           let uu____27714 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____27714 in
                         let uu____27715 =
                           FStar_Syntax_Print.term_to_string hd2 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____27713 uu____27715
                       else ());
                      (let uu____27717 = tc_term env2 hd2 in
                       match uu____27717 with
                       | (uu____27738,
                          { FStar_TypeChecker_Common.eff_name = uu____27739;
                            FStar_TypeChecker_Common.res_typ = t;
                            FStar_TypeChecker_Common.cflags = uu____27741;
                            FStar_TypeChecker_Common.comp_thunk = uu____27742;_},
                          g) ->
                           ((let uu____27760 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____27760
                               (fun uu____27761 -> ()));
                            (t, args1))))) in
          let uu____27772 = type_of_head true hd args in
          (match uu____27772 with
           | (t, args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t in
               let uu____27810 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____27810 with
                | (bs, res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst res1
                    else
                      (let uu____27836 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____27836)))
      | FStar_Syntax_Syntax.Tm_match (uu____27837, hd::uu____27839) ->
          let uu____27904 = FStar_Syntax_Subst.open_branch hd in
          (match uu____27904 with
           | (uu____27905, uu____27906, hd1) -> universe_of_aux env hd1)
      | FStar_Syntax_Syntax.Tm_match (uu____27924, []) ->
          level_of_type_fail env e "empty match cases"
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      let uu____27969 = universe_of_aux env e in
      level_of_type env e uu____27969
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env0 ->
    fun tps ->
      let uu____27992 = tc_binders env0 tps in
      match uu____27992 with
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
      | FStar_Syntax_Syntax.Tm_delayed uu____28049 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____28066 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____28071 = FStar_Syntax_Util.unfold_lazy i in
          type_of_well_typed_term env uu____28071
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____28073 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____28073
            (fun uu____28087 ->
               match uu____28087 with
               | (t2, uu____28095) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____28097;
             FStar_Syntax_Syntax.vars = uu____28098;_},
           us)
          ->
          let uu____28104 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____28104
            (fun uu____28118 ->
               match uu____28118 with
               | (t2, uu____28126) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____28127) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____28129 = tc_constant env t1.FStar_Syntax_Syntax.pos sc in
          FStar_Pervasives_Native.Some uu____28129
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____28131 = mk_tm_type (FStar_Syntax_Syntax.U_succ u) in
          FStar_Pervasives_Native.Some uu____28131
      | FStar_Syntax_Syntax.Tm_abs
          (bs, body, FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____28136;_})
          ->
          let mk_comp =
            let uu____28180 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid in
            if uu____28180
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____28208 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid in
               if uu____28208
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None) in
          FStar_Util.bind_opt mk_comp
            (fun f ->
               let uu____28275 = universe_of_well_typed_term env tbody in
               FStar_Util.bind_opt uu____28275
                 (fun u ->
                    let uu____28283 =
                      let uu____28286 =
                        let uu____28287 =
                          let uu____28302 =
                            f tbody (FStar_Pervasives_Native.Some u) in
                          (bs, uu____28302) in
                        FStar_Syntax_Syntax.Tm_arrow uu____28287 in
                      FStar_Syntax_Syntax.mk uu____28286
                        t1.FStar_Syntax_Syntax.pos in
                    FStar_Pervasives_Native.Some uu____28283))
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____28339 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____28339 with
           | (bs1, c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____28398 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1) in
                     FStar_Util.bind_opt uu____28398
                       (fun uc ->
                          let uu____28406 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us)) in
                          FStar_Pervasives_Native.Some uu____28406)
                 | (x, imp)::bs3 ->
                     let uu____28432 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort in
                     FStar_Util.bind_opt uu____28432
                       (fun u_x ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x in
                          aux env2 (u_x :: us) bs3) in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____28441 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x, uu____28461) ->
          let uu____28466 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort in
          FStar_Util.bind_opt uu____28466
            (fun u_x ->
               let uu____28474 = mk_tm_type u_x in
               FStar_Pervasives_Native.Some uu____28474)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____28479;
             FStar_Syntax_Syntax.vars = uu____28480;_},
           a::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____28559 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____28559 with
           | (unary_op, uu____28579) ->
               let head =
                 let uu____28607 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____28607 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____28655;
             FStar_Syntax_Syntax.vars = uu____28656;_},
           a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____28752 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____28752 with
           | (unary_op, uu____28772) ->
               let head =
                 let uu____28800 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   uu____28800 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____28856;
             FStar_Syntax_Syntax.vars = uu____28857;_},
           uu____28858::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____28897;
             FStar_Syntax_Syntax.vars = uu____28898;_},
           (t2, uu____28900)::uu____28901::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd, args) ->
          let t_hd = type_of_well_typed_term env hd in
          let rec aux t_hd1 =
            let uu____28997 =
              let uu____28998 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1 in
              uu____28998.FStar_Syntax_Syntax.n in
            match uu____28997 with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let n_args = FStar_List.length args in
                let n_bs = FStar_List.length bs in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____29070 = FStar_Util.first_N n_args bs in
                    match uu____29070 with
                    | (bs1, rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            t_hd1.FStar_Syntax_Syntax.pos in
                        let uu____29158 =
                          let uu____29163 = FStar_Syntax_Syntax.mk_Total t2 in
                          FStar_Syntax_Subst.open_comp bs1 uu____29163 in
                        (match uu____29158 with
                         | (bs2, c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____29215 = FStar_Syntax_Subst.open_comp bs c in
                       match uu____29215 with
                       | (bs1, c1) ->
                           let uu____29236 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1 in
                           if uu____29236
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____29314 ->
                     match uu____29314 with
                     | (bs1, t2) ->
                         let subst =
                           FStar_List.map2
                             (fun b ->
                                fun a ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args in
                         let uu____29390 = FStar_Syntax_Subst.subst subst t2 in
                         FStar_Pervasives_Native.Some uu____29390)
            | FStar_Syntax_Syntax.Tm_refine (x, uu____29392) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____29398, uu____29399)
                -> aux t2
            | uu____29440 -> FStar_Pervasives_Native.None in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29441, (FStar_Util.Inl t2, uu____29443), uu____29444) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29491, (FStar_Util.Inr c, uu____29493), uu____29494) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____29559 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
          FStar_Pervasives_Native.Some uu____29559
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____29567) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____29572 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____29595 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____29608 ->
          FStar_Pervasives_Native.None
and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let uu____29619 = type_of_well_typed_term env t in
      match uu____29619 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____29625;
            FStar_Syntax_Syntax.vars = uu____29626;_}
          -> FStar_Pervasives_Native.Some u
      | uu____29629 -> FStar_Pervasives_Native.None
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
            let uu___4156_29654 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4156_29654.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4156_29654.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4156_29654.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4156_29654.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4156_29654.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4156_29654.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4156_29654.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4156_29654.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4156_29654.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4156_29654.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4156_29654.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4156_29654.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4156_29654.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4156_29654.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4156_29654.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4156_29654.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4156_29654.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4156_29654.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4156_29654.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4156_29654.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4156_29654.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4156_29654.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4156_29654.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4156_29654.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4156_29654.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4156_29654.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4156_29654.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4156_29654.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4156_29654.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4156_29654.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4156_29654.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4156_29654.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4156_29654.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4156_29654.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4156_29654.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4156_29654.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4156_29654.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4156_29654.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4156_29654.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4156_29654.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4156_29654.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4156_29654.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4156_29654.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4156_29654.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4156_29654.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4156_29654.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let slow_check uu____29660 =
            if must_total
            then
              let uu____29661 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____29661 with | (uu____29668, uu____29669, g) -> g
            else
              (let uu____29672 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____29672 with | (uu____29679, uu____29680, g) -> g) in
          let uu____29682 = type_of_well_typed_term env2 t in
          match uu____29682 with
          | FStar_Pervasives_Native.None -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____29687 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits") in
                if uu____29687
                then
                  let uu____29688 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                  let uu____29689 = FStar_Syntax_Print.term_to_string t in
                  let uu____29690 = FStar_Syntax_Print.term_to_string k' in
                  let uu____29691 = FStar_Syntax_Print.term_to_string k in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____29688 uu____29689 uu____29690 uu____29691
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k in
                (let uu____29697 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits") in
                 if uu____29697
                 then
                   let uu____29698 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                   let uu____29699 = FStar_Syntax_Print.term_to_string t in
                   let uu____29700 = FStar_Syntax_Print.term_to_string k' in
                   let uu____29701 = FStar_Syntax_Print.term_to_string k in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____29698
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____29699 uu____29700 uu____29701
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
            let uu___4187_29727 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4187_29727.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4187_29727.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4187_29727.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4187_29727.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4187_29727.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4187_29727.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4187_29727.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4187_29727.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4187_29727.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4187_29727.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4187_29727.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4187_29727.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4187_29727.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4187_29727.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4187_29727.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4187_29727.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4187_29727.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4187_29727.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4187_29727.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4187_29727.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4187_29727.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4187_29727.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4187_29727.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4187_29727.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4187_29727.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4187_29727.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4187_29727.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4187_29727.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4187_29727.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4187_29727.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4187_29727.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4187_29727.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4187_29727.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4187_29727.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4187_29727.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4187_29727.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4187_29727.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4187_29727.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4187_29727.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4187_29727.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4187_29727.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4187_29727.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4187_29727.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4187_29727.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4187_29727.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4187_29727.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let slow_check uu____29733 =
            if must_total
            then
              let uu____29734 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____29734 with | (uu____29741, uu____29742, g) -> g
            else
              (let uu____29745 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____29745 with | (uu____29752, uu____29753, g) -> g) in
          let uu____29755 =
            let uu____29756 = FStar_Options.__temp_fast_implicits () in
            FStar_All.pipe_left Prims.op_Negation uu____29756 in
          if uu____29755
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k