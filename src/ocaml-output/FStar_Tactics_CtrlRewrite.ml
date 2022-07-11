open Prims
type controller_ty =
  FStar_Syntax_Syntax.term ->
    (Prims.bool * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac
type rewriter_ty = unit FStar_Tactics_Monad.tac
let (rangeof : FStar_Tactics_Types.goal -> FStar_Compiler_Range.range) =
  fun g ->
    (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
let (__do_rewrite :
  FStar_Tactics_Types.goal ->
    rewriter_ty ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun rewriter ->
      fun env ->
        fun tm ->
          let should_skip =
            let uu___ =
              let uu___1 = FStar_Syntax_Subst.compress tm in
              uu___1.FStar_Syntax_Syntax.n in
            match uu___ with
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                true
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
                uu___1) -> true
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of) ->
                true
            | FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of) -> true
            | uu___1 -> false in
          if should_skip
          then FStar_Tactics_Monad.ret tm
          else
            (let res =
               try
                 (fun uu___1 ->
                    match () with
                    | () ->
                        FStar_Errors.with_ctx
                          "While typechecking a subterm for ctrl_rewrite"
                          (fun uu___2 ->
                             let uu___3 =
                               env.FStar_TypeChecker_Env.tc_term
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (env.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (env.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (env.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (env.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (env.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (env.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (env.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (env.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (env.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (env.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (env.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (env.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (env.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (env.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (env.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (env.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (env.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (env.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (env.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (env.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (env.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (env.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (env.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (env.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (env.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                     =
                                     (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                   FStar_TypeChecker_Env.universe_of =
                                     (env.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                     =
                                     (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                   FStar_TypeChecker_Env.teq_nosmt_force =
                                     (env.FStar_TypeChecker_Env.teq_nosmt_force);
                                   FStar_TypeChecker_Env.subtype_nosmt_force
                                     =
                                     (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (env.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (env.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (env.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (env.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (env.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (env.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (env.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (env.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (env.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (env.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (env.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (env.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (env.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (env.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                                   FStar_TypeChecker_Env.unif_allow_ref_guards
                                     =
                                     (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                   FStar_TypeChecker_Env.erase_erasable_args
                                     =
                                     (env.FStar_TypeChecker_Env.erase_erasable_args);
                                   FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar
                                     =
                                     (env.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
                                 } tm in
                             FStar_Pervasives_Native.Some uu___3)) ()
               with
               | FStar_Errors.Error
                   (FStar_Errors.Error_LayeredMissingAnnot, uu___2, uu___3,
                    uu___4)
                   -> FStar_Pervasives_Native.None
               | e -> FStar_Compiler_Effect.raise e in
             match res with
             | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret tm
             | FStar_Pervasives_Native.Some (uu___1, lcomp, g) ->
                 let uu___2 =
                   let uu___3 =
                     FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu___3 in
                 if uu___2
                 then FStar_Tactics_Monad.ret tm
                 else
                   (let typ = lcomp.FStar_TypeChecker_Common.res_typ in
                    let uu___4 =
                      FStar_Tactics_Monad.new_uvar "do_rewrite.rhs" env typ
                        FStar_Pervasives_Native.None [] (rangeof g0) in
                    FStar_Tactics_Monad.bind uu___4
                      (fun uu___5 ->
                         match uu___5 with
                         | (ut, uvar_ut) ->
                             FStar_Tactics_Monad.mlog
                               (fun uu___6 ->
                                  let uu___7 =
                                    FStar_Syntax_Print.term_to_string tm in
                                  let uu___8 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Compiler_Util.print2
                                    "do_rewrite: making equality\n\t%s ==\n\t%s\n"
                                    uu___7 uu___8)
                               (fun uu___6 ->
                                  let uu___7 =
                                    let uu___8 =
                                      let uu___9 =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env typ in
                                      FStar_Syntax_Util.mk_eq2 uu___9 typ tm
                                        ut in
                                    FStar_Tactics_Monad.add_irrelevant_goal
                                      g0 "do_rewrite.eq" env uu___8 in
                                  FStar_Tactics_Monad.bind uu___7
                                    (fun uu___8 ->
                                       let uu___9 =
                                         FStar_Tactics_Basic.focus rewriter in
                                       FStar_Tactics_Monad.bind uu___9
                                         (fun uu___10 ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut in
                                            FStar_Tactics_Monad.mlog
                                              (fun uu___11 ->
                                                 let uu___12 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm in
                                                 let uu___13 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1 in
                                                 FStar_Compiler_Util.print2
                                                   "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu___12 uu___13)
                                              (fun uu___11 ->
                                                 FStar_Tactics_Monad.ret ut1)))))))
let (do_rewrite :
  FStar_Tactics_Types.goal ->
    rewriter_ty ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun rewriter ->
      fun env ->
        fun tm ->
          let uu___ =
            let uu___1 = __do_rewrite g0 rewriter env tm in
            FStar_Tactics_Monad.catch uu___1 in
          FStar_Tactics_Monad.bind uu___
            (fun uu___1 ->
               match uu___1 with
               | FStar_Pervasives.Inl (FStar_Tactics_Common.TacticFailure
                   "SKIP") -> FStar_Tactics_Monad.ret tm
               | FStar_Pervasives.Inl e -> FStar_Tactics_Monad.traise e
               | FStar_Pervasives.Inr tm' -> FStar_Tactics_Monad.ret tm')
type 'a ctac =
  'a -> ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac
let seq_ctac : 'a . 'a ctac -> 'a ctac -> 'a ctac =
  fun c1 ->
    fun c2 ->
      fun x ->
        let uu___ = c1 x in
        FStar_Tactics_Monad.bind uu___
          (fun uu___1 ->
             match uu___1 with
             | (x', flag) ->
                 (match flag with
                  | FStar_Tactics_Types.Abort ->
                      FStar_Tactics_Monad.ret (x', FStar_Tactics_Types.Abort)
                  | FStar_Tactics_Types.Skip ->
                      FStar_Tactics_Monad.ret (x', FStar_Tactics_Types.Skip)
                  | FStar_Tactics_Types.Continue -> c2 x'))
let (par_combine :
  (FStar_Tactics_Types.ctrl_flag * FStar_Tactics_Types.ctrl_flag) ->
    FStar_Tactics_Types.ctrl_flag)
  =
  fun uu___ ->
    match uu___ with
    | (FStar_Tactics_Types.Abort, uu___1) -> FStar_Tactics_Types.Abort
    | (uu___1, FStar_Tactics_Types.Abort) -> FStar_Tactics_Types.Abort
    | (FStar_Tactics_Types.Skip, uu___1) -> FStar_Tactics_Types.Skip
    | (uu___1, FStar_Tactics_Types.Skip) -> FStar_Tactics_Types.Skip
    | (FStar_Tactics_Types.Continue, FStar_Tactics_Types.Continue) ->
        FStar_Tactics_Types.Continue
let par_ctac : 'a 'b . 'a ctac -> 'b ctac -> ('a * 'b) ctac =
  fun cl ->
    fun cr ->
      fun uu___ ->
        match uu___ with
        | (x, y) ->
            let uu___1 = cl x in
            FStar_Tactics_Monad.bind uu___1
              (fun uu___2 ->
                 match uu___2 with
                 | (x1, flag) ->
                     (match flag with
                      | FStar_Tactics_Types.Abort ->
                          FStar_Tactics_Monad.ret
                            ((x1, y), FStar_Tactics_Types.Abort)
                      | fa ->
                          let uu___3 = cr y in
                          FStar_Tactics_Monad.bind uu___3
                            (fun uu___4 ->
                               match uu___4 with
                               | (y1, flag1) ->
                                   (match flag1 with
                                    | FStar_Tactics_Types.Abort ->
                                        FStar_Tactics_Monad.ret
                                          ((x1, y1),
                                            FStar_Tactics_Types.Abort)
                                    | fb ->
                                        FStar_Tactics_Monad.ret
                                          ((x1, y1), (par_combine (fa, fb)))))))
let rec map_ctac : 'a . 'a ctac -> 'a Prims.list ctac =
  fun c ->
    fun xs ->
      match xs with
      | [] -> FStar_Tactics_Monad.ret ([], FStar_Tactics_Types.Continue)
      | x::xs1 ->
          let uu___ =
            let uu___1 = let uu___2 = map_ctac c in par_ctac c uu___2 in
            uu___1 (x, xs1) in
          FStar_Tactics_Monad.bind uu___
            (fun uu___1 ->
               match uu___1 with
               | ((x1, xs2), flag) ->
                   FStar_Tactics_Monad.ret ((x1 :: xs2), flag))
let ctac_id :
  'a . 'a -> ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac =
  fun x -> FStar_Tactics_Monad.ret (x, FStar_Tactics_Types.Continue)
let (ctac_args :
  FStar_Syntax_Syntax.term ctac -> FStar_Syntax_Syntax.args ctac) =
  fun c -> let uu___ = par_ctac c ctac_id in map_ctac uu___
let (maybe_rewrite :
  FStar_Tactics_Types.goal ->
    controller_ty ->
      rewriter_ty ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Tactics_Types.ctrl_flag)
              FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun controller ->
      fun rewriter ->
        fun env ->
          fun tm ->
            let uu___ = controller tm in
            FStar_Tactics_Monad.bind uu___
              (fun uu___1 ->
                 match uu___1 with
                 | (rw, ctrl_flag) ->
                     let uu___2 =
                       if rw
                       then do_rewrite g0 rewriter env tm
                       else FStar_Tactics_Monad.ret tm in
                     FStar_Tactics_Monad.bind uu___2
                       (fun tm' -> FStar_Tactics_Monad.ret (tm', ctrl_flag)))
let rec (ctrl_fold_env :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term ->
              (FStar_Syntax_Syntax.term * FStar_Tactics_Types.ctrl_flag)
                FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun d ->
      fun controller ->
        fun rewriter ->
          fun env ->
            fun tm ->
              let recurse tm1 =
                ctrl_fold_env g0 d controller rewriter env tm1 in
              match d with
              | FStar_Tactics_Types.TopDown ->
                  let uu___ =
                    seq_ctac (maybe_rewrite g0 controller rewriter env)
                      (on_subterms g0 d controller rewriter env) in
                  uu___ tm
              | FStar_Tactics_Types.BottomUp ->
                  let uu___ =
                    seq_ctac (on_subterms g0 d controller rewriter env)
                      (maybe_rewrite g0 controller rewriter env) in
                  uu___ tm
and (recurse_option_residual_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        (FStar_TypeChecker_Env.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
               FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac)
          ->
          (FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
            FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac)
  =
  fun env ->
    fun retyping_subst ->
      fun rc_opt ->
        fun recurse ->
          match rc_opt with
          | FStar_Pervasives_Native.None ->
              FStar_Tactics_Monad.ret
                (FStar_Pervasives_Native.None, FStar_Tactics_Types.Continue)
          | FStar_Pervasives_Native.Some rc ->
              (match rc.FStar_Syntax_Syntax.residual_typ with
               | FStar_Pervasives_Native.None ->
                   FStar_Tactics_Monad.ret
                     ((FStar_Pervasives_Native.Some rc),
                       FStar_Tactics_Types.Continue)
               | FStar_Pervasives_Native.Some t ->
                   let t1 = FStar_Syntax_Subst.subst retyping_subst t in
                   let uu___ = recurse env t1 in
                   FStar_Tactics_Monad.bind uu___
                     (fun uu___1 ->
                        match uu___1 with
                        | (t2, flag) ->
                            FStar_Tactics_Monad.ret
                              ((FStar_Pervasives_Native.Some
                                  {
                                    FStar_Syntax_Syntax.residual_effect =
                                      (rc.FStar_Syntax_Syntax.residual_effect);
                                    FStar_Syntax_Syntax.residual_typ =
                                      (FStar_Pervasives_Native.Some t2);
                                    FStar_Syntax_Syntax.residual_flags =
                                      (rc.FStar_Syntax_Syntax.residual_flags)
                                  }), flag)))
and (on_subterms :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term ->
              (FStar_Syntax_Syntax.term * FStar_Tactics_Types.ctrl_flag)
                FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun d ->
      fun controller ->
        fun rewriter ->
          fun env ->
            fun tm ->
              let recurse env1 tm1 =
                ctrl_fold_env g0 d controller rewriter env1 tm1 in
              let rr = recurse env in
              let rec descend_binders orig accum_binders retyping_subst
                accum_flag env1 bs t k rebuild =
                match bs with
                | [] ->
                    let t1 = FStar_Syntax_Subst.subst retyping_subst t in
                    let uu___ = recurse env1 t1 in
                    FStar_Tactics_Monad.bind uu___
                      (fun uu___1 ->
                         match uu___1 with
                         | (t2, t_flag) ->
                             (match t_flag with
                              | FStar_Tactics_Types.Abort ->
                                  FStar_Tactics_Monad.ret
                                    ((orig.FStar_Syntax_Syntax.n), t_flag)
                              | uu___2 ->
                                  let uu___3 =
                                    recurse_option_residual_comp env1
                                      retyping_subst k recurse in
                                  FStar_Tactics_Monad.bind uu___3
                                    (fun uu___4 ->
                                       match uu___4 with
                                       | (k1, k_flag) ->
                                           let bs1 =
                                             FStar_Compiler_List.rev
                                               accum_binders in
                                           let subst =
                                             FStar_Syntax_Subst.closing_of_binders
                                               bs1 in
                                           let bs2 =
                                             FStar_Syntax_Subst.subst_binders
                                               subst bs1 in
                                           let t3 =
                                             FStar_Syntax_Subst.subst subst
                                               t2 in
                                           let k2 =
                                             FStar_Compiler_Util.map_option
                                               (FStar_Syntax_Subst.subst_residual_comp
                                                  subst) k1 in
                                           let uu___5 =
                                             let uu___6 = rebuild bs2 t3 k2 in
                                             (uu___6,
                                               (par_combine
                                                  (accum_flag,
                                                    (par_combine
                                                       (t_flag, k_flag))))) in
                                           FStar_Tactics_Monad.ret uu___5)))
                | b::bs1 ->
                    let s =
                      FStar_Syntax_Subst.subst retyping_subst
                        (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                    let uu___ = recurse env1 s in
                    FStar_Tactics_Monad.bind uu___
                      (fun uu___1 ->
                         match uu___1 with
                         | (s1, flag) ->
                             (match flag with
                              | FStar_Tactics_Types.Abort ->
                                  FStar_Tactics_Monad.ret
                                    ((orig.FStar_Syntax_Syntax.n), flag)
                              | uu___2 ->
                                  let bv =
                                    let uu___3 =
                                      b.FStar_Syntax_Syntax.binder_bv in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___3.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___3.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = s1
                                    } in
                                  let b1 =
                                    {
                                      FStar_Syntax_Syntax.binder_bv = bv;
                                      FStar_Syntax_Syntax.binder_qual =
                                        (b.FStar_Syntax_Syntax.binder_qual);
                                      FStar_Syntax_Syntax.binder_attrs =
                                        (b.FStar_Syntax_Syntax.binder_attrs)
                                    } in
                                  let env2 =
                                    FStar_TypeChecker_Env.push_binders env1
                                      [b1] in
                                  let retyping_subst1 =
                                    let uu___3 =
                                      let uu___4 =
                                        let uu___5 =
                                          FStar_Syntax_Syntax.bv_to_name bv in
                                        (bv, uu___5) in
                                      FStar_Syntax_Syntax.NT uu___4 in
                                    uu___3 :: retyping_subst in
                                  descend_binders orig (b1 :: accum_binders)
                                    retyping_subst1
                                    (par_combine (accum_flag, flag)) env2 bs1
                                    t k rebuild)) in
              let go uu___ =
                let tm1 = FStar_Syntax_Subst.compress tm in
                match tm1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_app (hd, args) ->
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = ctac_args rr in par_ctac rr uu___3 in
                      uu___2 (hd, args) in
                    FStar_Tactics_Monad.bind uu___1
                      (fun uu___2 ->
                         match uu___2 with
                         | ((hd1, args1), flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_app (hd1, args1)),
                                 flag))
                | FStar_Syntax_Syntax.Tm_abs (bs, t, k) ->
                    let uu___1 = FStar_Syntax_Subst.open_term' bs t in
                    (match uu___1 with
                     | (bs_orig, t1, subst) ->
                         let k1 =
                           FStar_Compiler_Effect.op_Bar_Greater k
                             (FStar_Compiler_Util.map_option
                                (FStar_Syntax_Subst.subst_residual_comp subst)) in
                         descend_binders tm1 [] []
                           FStar_Tactics_Types.Continue env bs_orig t1 k1
                           (fun bs1 ->
                              fun t2 ->
                                fun k2 ->
                                  FStar_Syntax_Syntax.Tm_abs (bs1, t2, k2)))
                | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = FStar_Syntax_Syntax.mk_binder x in
                        [uu___3] in
                      FStar_Syntax_Subst.open_term uu___2 phi in
                    (match uu___1 with
                     | (bs, phi1) ->
                         descend_binders tm1 [] []
                           FStar_Tactics_Types.Continue env bs phi1
                           FStar_Pervasives_Native.None
                           (fun bs1 ->
                              fun phi2 ->
                                fun uu___2 ->
                                  let x1 =
                                    match bs1 with
                                    | x2::[] ->
                                        x2.FStar_Syntax_Syntax.binder_bv
                                    | uu___3 -> failwith "Impossible" in
                                  FStar_Syntax_Syntax.Tm_refine (x1, phi2)))
                | FStar_Syntax_Syntax.Tm_arrow (bs, k) ->
                    FStar_Tactics_Monad.ret
                      ((tm1.FStar_Syntax_Syntax.n),
                        FStar_Tactics_Types.Continue)
                | FStar_Syntax_Syntax.Tm_match (hd, asc_opt, brs, lopt) ->
                    let c_branch br =
                      let uu___1 = FStar_Syntax_Subst.open_branch br in
                      match uu___1 with
                      | (pat, w, e) ->
                          let bvs = FStar_Syntax_Syntax.pat_bvs pat in
                          let uu___2 =
                            let uu___3 =
                              FStar_TypeChecker_Env.push_bvs env bvs in
                            recurse uu___3 e in
                          FStar_Tactics_Monad.bind uu___2
                            (fun uu___3 ->
                               match uu___3 with
                               | (e1, flag) ->
                                   let br1 =
                                     FStar_Syntax_Subst.close_branch
                                       (pat, w, e1) in
                                   FStar_Tactics_Monad.ret (br1, flag)) in
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = map_ctac c_branch in par_ctac rr uu___3 in
                      uu___2 (hd, brs) in
                    FStar_Tactics_Monad.bind uu___1
                      (fun uu___2 ->
                         match uu___2 with
                         | ((hd1, brs1), flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_match
                                   (hd1, asc_opt, brs1, lopt)), flag))
                | FStar_Syntax_Syntax.Tm_let
                    ((false,
                      { FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inl bv;
                        FStar_Syntax_Syntax.lbunivs = uu___1;
                        FStar_Syntax_Syntax.lbtyp = uu___2;
                        FStar_Syntax_Syntax.lbeff = uu___3;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu___4;
                        FStar_Syntax_Syntax.lbpos = uu___5;_}::[]),
                     e)
                    ->
                    let lb =
                      let uu___6 =
                        let uu___7 = FStar_Syntax_Subst.compress tm1 in
                        uu___7.FStar_Syntax_Syntax.n in
                      match uu___6 with
                      | FStar_Syntax_Syntax.Tm_let ((false, lb1::[]), uu___7)
                          -> lb1
                      | uu___7 -> failwith "impossible" in
                    let uu___6 = FStar_Syntax_Subst.open_term_bv bv e in
                    (match uu___6 with
                     | (bv1, e1) ->
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 FStar_TypeChecker_Env.push_bv env bv1 in
                               recurse uu___10 in
                             par_ctac rr uu___9 in
                           uu___8 ((lb.FStar_Syntax_Syntax.lbdef), e1) in
                         FStar_Tactics_Monad.bind uu___7
                           (fun uu___8 ->
                              match uu___8 with
                              | ((lbdef, e2), flag) ->
                                  let lb1 =
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (lb.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (lb.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (lb.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (lb.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = lbdef;
                                      FStar_Syntax_Syntax.lbattrs =
                                        (lb.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (lb.FStar_Syntax_Syntax.lbpos)
                                    } in
                                  let e3 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_Syntax_Syntax.mk_binder bv1 in
                                      [uu___10] in
                                    FStar_Syntax_Subst.close uu___9 e2 in
                                  FStar_Tactics_Monad.ret
                                    ((FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3)), flag)))
                | FStar_Syntax_Syntax.Tm_let ((true, lbs), e) ->
                    let c_lb lb =
                      let uu___1 = rr lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Tactics_Monad.bind uu___1
                        (fun uu___2 ->
                           match uu___2 with
                           | (def, flag) ->
                               FStar_Tactics_Monad.ret
                                 ({
                                    FStar_Syntax_Syntax.lbname =
                                      (lb.FStar_Syntax_Syntax.lbname);
                                    FStar_Syntax_Syntax.lbunivs =
                                      (lb.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp =
                                      (lb.FStar_Syntax_Syntax.lbtyp);
                                    FStar_Syntax_Syntax.lbeff =
                                      (lb.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (lb.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (lb.FStar_Syntax_Syntax.lbpos)
                                  }, flag)) in
                    let uu___1 = FStar_Syntax_Subst.open_let_rec lbs e in
                    (match uu___1 with
                     | (lbs1, e1) ->
                         let uu___2 =
                           let uu___3 =
                             let uu___4 = map_ctac c_lb in par_ctac uu___4 rr in
                           uu___3 (lbs1, e1) in
                         FStar_Tactics_Monad.bind uu___2
                           (fun uu___3 ->
                              match uu___3 with
                              | ((lbs2, e2), flag) ->
                                  let uu___4 =
                                    FStar_Syntax_Subst.close_let_rec lbs2 e2 in
                                  (match uu___4 with
                                   | (lbs3, e3) ->
                                       FStar_Tactics_Monad.ret
                                         ((FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)), flag))))
                | FStar_Syntax_Syntax.Tm_ascribed (t, asc, eff) ->
                    let uu___1 = rr t in
                    FStar_Tactics_Monad.bind uu___1
                      (fun uu___2 ->
                         match uu___2 with
                         | (t1, flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_ascribed
                                   (t1, asc, eff)), flag))
                | FStar_Syntax_Syntax.Tm_meta (t, m) ->
                    let uu___1 = rr t in
                    FStar_Tactics_Monad.bind uu___1
                      (fun uu___2 ->
                         match uu___2 with
                         | (t1, flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_meta (t1, m)), flag))
                | uu___1 ->
                    FStar_Tactics_Monad.ret
                      ((tm1.FStar_Syntax_Syntax.n),
                        FStar_Tactics_Types.Continue) in
              let uu___ = go () in
              FStar_Tactics_Monad.bind uu___
                (fun uu___1 ->
                   match uu___1 with
                   | (tmn', flag) ->
                       FStar_Tactics_Monad.ret
                         ({
                            FStar_Syntax_Syntax.n = tmn';
                            FStar_Syntax_Syntax.pos =
                              (tm.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (tm.FStar_Syntax_Syntax.vars)
                          }, flag))
let (do_ctrl_rewrite :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun dir ->
      fun controller ->
        fun rewriter ->
          fun env ->
            fun tm ->
              let uu___ = ctrl_fold_env g0 dir controller rewriter env tm in
              FStar_Tactics_Monad.bind uu___
                (fun uu___1 ->
                   match uu___1 with
                   | (tm', uu___2) -> FStar_Tactics_Monad.ret tm')
let (ctrl_rewrite :
  FStar_Tactics_Types.direction ->
    controller_ty -> rewriter_ty -> unit FStar_Tactics_Monad.tac)
  =
  fun dir ->
    fun controller ->
      fun rewriter ->
        let uu___ =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu___1 =
                 match ps.FStar_Tactics_Types.goals with
                 | g::gs -> (g, gs)
                 | [] -> failwith "no goals" in
               match uu___1 with
               | (g, gs) ->
                   FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss_all
                     (fun uu___2 ->
                        let gt = FStar_Tactics_Types.goal_type g in
                        FStar_Tactics_Monad.log ps
                          (fun uu___4 ->
                             let uu___5 =
                               FStar_Syntax_Print.term_to_string gt in
                             FStar_Compiler_Util.print1
                               "ctrl_rewrite starting with %s\n" uu___5);
                        (let uu___4 =
                           let uu___5 = FStar_Tactics_Types.goal_env g in
                           do_ctrl_rewrite g dir controller rewriter uu___5
                             gt in
                         FStar_Tactics_Monad.bind uu___4
                           (fun gt' ->
                              FStar_Tactics_Monad.log ps
                                (fun uu___6 ->
                                   let uu___7 =
                                     FStar_Syntax_Print.term_to_string gt' in
                                   FStar_Compiler_Util.print1
                                     "ctrl_rewrite seems to have succeded with %s\n"
                                     uu___7);
                              (let uu___6 = FStar_Tactics_Monad.push_goals gs in
                               FStar_Tactics_Monad.bind uu___6
                                 (fun uu___7 ->
                                    let g1 =
                                      FStar_Tactics_Basic.goal_with_type g
                                        gt' in
                                    FStar_Tactics_Monad.add_goals [g1])))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "ctrl_rewrite") uu___