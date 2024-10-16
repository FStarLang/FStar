open Prims
type controller_ty =
  FStarC_Syntax_Syntax.term ->
    (Prims.bool * FStarC_Tactics_Types.ctrl_flag) FStarC_Tactics_Monad.tac
type rewriter_ty = unit FStarC_Tactics_Monad.tac
let (rangeof : FStarC_Tactics_Types.goal -> FStarC_Compiler_Range_Type.range)
  =
  fun g ->
    (g.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_range
let (__do_rewrite :
  FStarC_Tactics_Types.goal ->
    rewriter_ty ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g0 ->
             fun rewriter ->
               fun env ->
                 fun tm ->
                   let should_skip =
                     let uu___ =
                       let uu___1 = FStarC_Syntax_Subst.compress tm in
                       uu___1.FStarC_Syntax_Syntax.n in
                     match uu___ with
                     | FStarC_Syntax_Syntax.Tm_constant
                         (FStarC_Const.Const_reify uu___1) -> true
                     | FStarC_Syntax_Syntax.Tm_constant
                         (FStarC_Const.Const_reflect uu___1) -> true
                     | FStarC_Syntax_Syntax.Tm_constant
                         (FStarC_Const.Const_range_of) -> true
                     | FStarC_Syntax_Syntax.Tm_constant
                         (FStarC_Const.Const_set_range_of) -> true
                     | uu___1 -> false in
                   if should_skip
                   then
                     Obj.magic
                       (FStarC_Class_Monad.return
                          FStarC_Tactics_Monad.monad_tac () (Obj.magic tm))
                   else
                     (let res =
                        try
                          (fun uu___1 ->
                             match () with
                             | () ->
                                 FStarC_Errors.with_ctx
                                   "While typechecking a subterm for ctrl_rewrite"
                                   (fun uu___2 ->
                                      let uu___3 =
                                        env.FStarC_TypeChecker_Env.tc_term
                                          {
                                            FStarC_TypeChecker_Env.solver =
                                              (env.FStarC_TypeChecker_Env.solver);
                                            FStarC_TypeChecker_Env.range =
                                              (env.FStarC_TypeChecker_Env.range);
                                            FStarC_TypeChecker_Env.curmodule
                                              =
                                              (env.FStarC_TypeChecker_Env.curmodule);
                                            FStarC_TypeChecker_Env.gamma =
                                              (env.FStarC_TypeChecker_Env.gamma);
                                            FStarC_TypeChecker_Env.gamma_sig
                                              =
                                              (env.FStarC_TypeChecker_Env.gamma_sig);
                                            FStarC_TypeChecker_Env.gamma_cache
                                              =
                                              (env.FStarC_TypeChecker_Env.gamma_cache);
                                            FStarC_TypeChecker_Env.modules =
                                              (env.FStarC_TypeChecker_Env.modules);
                                            FStarC_TypeChecker_Env.expected_typ
                                              =
                                              (env.FStarC_TypeChecker_Env.expected_typ);
                                            FStarC_TypeChecker_Env.sigtab =
                                              (env.FStarC_TypeChecker_Env.sigtab);
                                            FStarC_TypeChecker_Env.attrtab =
                                              (env.FStarC_TypeChecker_Env.attrtab);
                                            FStarC_TypeChecker_Env.instantiate_imp
                                              =
                                              (env.FStarC_TypeChecker_Env.instantiate_imp);
                                            FStarC_TypeChecker_Env.effects =
                                              (env.FStarC_TypeChecker_Env.effects);
                                            FStarC_TypeChecker_Env.generalize
                                              =
                                              (env.FStarC_TypeChecker_Env.generalize);
                                            FStarC_TypeChecker_Env.letrecs =
                                              (env.FStarC_TypeChecker_Env.letrecs);
                                            FStarC_TypeChecker_Env.top_level
                                              =
                                              (env.FStarC_TypeChecker_Env.top_level);
                                            FStarC_TypeChecker_Env.check_uvars
                                              =
                                              (env.FStarC_TypeChecker_Env.check_uvars);
                                            FStarC_TypeChecker_Env.use_eq_strict
                                              =
                                              (env.FStarC_TypeChecker_Env.use_eq_strict);
                                            FStarC_TypeChecker_Env.is_iface =
                                              (env.FStarC_TypeChecker_Env.is_iface);
                                            FStarC_TypeChecker_Env.admit =
                                              true;
                                            FStarC_TypeChecker_Env.lax_universes
                                              =
                                              (env.FStarC_TypeChecker_Env.lax_universes);
                                            FStarC_TypeChecker_Env.phase1 =
                                              (env.FStarC_TypeChecker_Env.phase1);
                                            FStarC_TypeChecker_Env.failhard =
                                              (env.FStarC_TypeChecker_Env.failhard);
                                            FStarC_TypeChecker_Env.flychecking
                                              =
                                              (env.FStarC_TypeChecker_Env.flychecking);
                                            FStarC_TypeChecker_Env.uvar_subtyping
                                              =
                                              (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                            FStarC_TypeChecker_Env.intactics
                                              =
                                              (env.FStarC_TypeChecker_Env.intactics);
                                            FStarC_TypeChecker_Env.nocoerce =
                                              (env.FStarC_TypeChecker_Env.nocoerce);
                                            FStarC_TypeChecker_Env.tc_term =
                                              (env.FStarC_TypeChecker_Env.tc_term);
                                            FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                              =
                                              (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                            FStarC_TypeChecker_Env.universe_of
                                              =
                                              (env.FStarC_TypeChecker_Env.universe_of);
                                            FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                              =
                                              (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                            FStarC_TypeChecker_Env.teq_nosmt_force
                                              =
                                              (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                            FStarC_TypeChecker_Env.subtype_nosmt_force
                                              =
                                              (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                            FStarC_TypeChecker_Env.qtbl_name_and_index
                                              =
                                              (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                            FStarC_TypeChecker_Env.normalized_eff_names
                                              =
                                              (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                            FStarC_TypeChecker_Env.fv_delta_depths
                                              =
                                              (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                            FStarC_TypeChecker_Env.proof_ns =
                                              (env.FStarC_TypeChecker_Env.proof_ns);
                                            FStarC_TypeChecker_Env.synth_hook
                                              =
                                              (env.FStarC_TypeChecker_Env.synth_hook);
                                            FStarC_TypeChecker_Env.try_solve_implicits_hook
                                              =
                                              (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                            FStarC_TypeChecker_Env.splice =
                                              (env.FStarC_TypeChecker_Env.splice);
                                            FStarC_TypeChecker_Env.mpreprocess
                                              =
                                              (env.FStarC_TypeChecker_Env.mpreprocess);
                                            FStarC_TypeChecker_Env.postprocess
                                              =
                                              (env.FStarC_TypeChecker_Env.postprocess);
                                            FStarC_TypeChecker_Env.identifier_info
                                              =
                                              (env.FStarC_TypeChecker_Env.identifier_info);
                                            FStarC_TypeChecker_Env.tc_hooks =
                                              (env.FStarC_TypeChecker_Env.tc_hooks);
                                            FStarC_TypeChecker_Env.dsenv =
                                              (env.FStarC_TypeChecker_Env.dsenv);
                                            FStarC_TypeChecker_Env.nbe =
                                              (env.FStarC_TypeChecker_Env.nbe);
                                            FStarC_TypeChecker_Env.strict_args_tab
                                              =
                                              (env.FStarC_TypeChecker_Env.strict_args_tab);
                                            FStarC_TypeChecker_Env.erasable_types_tab
                                              =
                                              (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                            FStarC_TypeChecker_Env.enable_defer_to_tac
                                              =
                                              (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                            FStarC_TypeChecker_Env.unif_allow_ref_guards
                                              =
                                              (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                            FStarC_TypeChecker_Env.erase_erasable_args
                                              =
                                              (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                            FStarC_TypeChecker_Env.core_check
                                              =
                                              (env.FStarC_TypeChecker_Env.core_check);
                                            FStarC_TypeChecker_Env.missing_decl
                                              =
                                              (env.FStarC_TypeChecker_Env.missing_decl)
                                          } tm in
                                      FStar_Pervasives_Native.Some uu___3))
                            ()
                        with
                        | FStarC_Errors.Error
                            (FStarC_Errors_Codes.Error_LayeredMissingAnnot,
                             uu___2, uu___3, uu___4)
                            -> FStar_Pervasives_Native.None
                        | e -> FStarC_Compiler_Effect.raise e in
                      match res with
                      | FStar_Pervasives_Native.None ->
                          Obj.magic
                            (FStarC_Class_Monad.return
                               FStarC_Tactics_Monad.monad_tac ()
                               (Obj.magic tm))
                      | FStar_Pervasives_Native.Some (uu___1, lcomp, g) ->
                          let uu___2 =
                            let uu___3 =
                              FStarC_TypeChecker_Common.is_pure_or_ghost_lcomp
                                lcomp in
                            Prims.op_Negation uu___3 in
                          if uu___2
                          then
                            Obj.magic
                              (FStarC_Class_Monad.return
                                 FStarC_Tactics_Monad.monad_tac ()
                                 (Obj.magic tm))
                          else
                            (let g1 =
                               FStarC_TypeChecker_Rel.solve_deferred_constraints
                                 env g in
                             let typ =
                               lcomp.FStarC_TypeChecker_Common.res_typ in
                             let typ1 =
                               let uu___4 =
                                 let uu___5 =
                                   FStarC_Options_Ext.get "__unrefine" in
                                 uu___5 <> "" in
                               if uu___4
                               then
                                 let typ_norm =
                                   FStarC_TypeChecker_Normalize.unfold_whnf'
                                     [FStarC_TypeChecker_Env.DontUnfoldAttr
                                        [FStarC_Parser_Const.do_not_unrefine_attr]]
                                     env typ in
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       FStarC_Syntax_Subst.compress typ_norm in
                                     uu___7.FStarC_Syntax_Syntax.n in
                                   FStarC_Syntax_Syntax.uu___is_Tm_refine
                                     uu___6 in
                                 (if uu___5
                                  then
                                    let typ' =
                                      FStarC_TypeChecker_Normalize.unfold_whnf'
                                        [FStarC_TypeChecker_Env.DontUnfoldAttr
                                           [FStarC_Parser_Const.do_not_unrefine_attr];
                                        FStarC_TypeChecker_Env.Unrefine] env
                                        typ_norm in
                                    typ'
                                  else typ)
                               else typ in
                             let should_check =
                               let uu___4 =
                                 FStarC_TypeChecker_Common.is_total_lcomp
                                   lcomp in
                               if uu___4
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_Pervasives_Native.Some
                                   (FStarC_Syntax_Syntax.Allow_ghost
                                      "do_rewrite.lhs") in
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_Monad.goal_typedness_deps g0 in
                               FStarC_Tactics_Monad.new_uvar "do_rewrite.rhs"
                                 env typ1 should_check uu___5 (rangeof g0) in
                             Obj.magic
                               (FStarC_Class_Monad.op_let_Bang
                                  FStarC_Tactics_Monad.monad_tac () ()
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun uu___5 ->
                                        let uu___5 = Obj.magic uu___5 in
                                        match uu___5 with
                                        | (ut, uvar_t) ->
                                            let uu___6 =
                                              FStarC_Tactics_Monad.if_verbose
                                                (fun uu___7 ->
                                                   let uu___8 =
                                                     FStarC_Class_Show.show
                                                       FStarC_Syntax_Print.showable_term
                                                       tm in
                                                   let uu___9 =
                                                     FStarC_Class_Show.show
                                                       FStarC_Syntax_Print.showable_term
                                                       ut in
                                                   FStarC_Compiler_Util.print2
                                                     "do_rewrite: making equality\n\t%s ==\n\t%s\n"
                                                     uu___8 uu___9) in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Tactics_Monad.monad_tac
                                                 () () uu___6
                                                 (fun uu___7 ->
                                                    (fun uu___7 ->
                                                       let uu___7 =
                                                         Obj.magic uu___7 in
                                                       let uu___8 =
                                                         let uu___9 =
                                                           let uu___10 =
                                                             env.FStarC_TypeChecker_Env.universe_of
                                                               env typ1 in
                                                           FStarC_Syntax_Util.mk_eq2
                                                             uu___10 typ1 tm
                                                             ut in
                                                         FStarC_Tactics_Monad.add_irrelevant_goal
                                                           g0 "do_rewrite.eq"
                                                           env uu___9
                                                           FStar_Pervasives_Native.None in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Tactics_Monad.monad_tac
                                                            () () uu___8
                                                            (fun uu___9 ->
                                                               (fun uu___9 ->
                                                                  let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    uu___9 in
                                                                  let uu___10
                                                                    =
                                                                    FStarC_Tactics_Monad.focus
                                                                    rewriter in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___10
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    uu___11 in
                                                                    let ut1 =
                                                                    FStarC_TypeChecker_Normalize.reduce_uvar_solutions
                                                                    env ut in
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_Monad.if_verbose
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    tm in
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    ut1 in
                                                                    FStarC_Compiler_Util.print2
                                                                    "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                    uu___14
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___12
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    uu___13 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    ut1)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                 uu___9)))
                                                      uu___7))) uu___5)))))
            uu___3 uu___2 uu___1 uu___
let (do_rewrite :
  FStarC_Tactics_Types.goal ->
    rewriter_ty ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g0 ->
             fun rewriter ->
               fun env ->
                 fun tm ->
                   let uu___ =
                     let uu___1 = __do_rewrite g0 rewriter env tm in
                     FStarC_Tactics_Monad.catch uu___1 in
                   Obj.magic
                     (FStarC_Class_Monad.op_let_Bang
                        FStarC_Tactics_Monad.monad_tac () ()
                        (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun uu___1 ->
                              let uu___1 = Obj.magic uu___1 in
                              match uu___1 with
                              | FStar_Pervasives.Inl
                                  (FStarC_Tactics_Common.SKIP) ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStarC_Class_Monad.return
                                          FStarC_Tactics_Monad.monad_tac ()
                                          (Obj.magic tm)))
                              | FStar_Pervasives.Inl e ->
                                  Obj.magic
                                    (Obj.repr (FStarC_Tactics_Monad.traise e))
                              | FStar_Pervasives.Inr tm' ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStarC_Class_Monad.return
                                          FStarC_Tactics_Monad.monad_tac ()
                                          (Obj.magic tm')))) uu___1))) uu___3
            uu___2 uu___1 uu___
type 'a ctac =
  'a -> ('a * FStarC_Tactics_Types.ctrl_flag) FStarC_Tactics_Monad.tac
let seq_ctac : 'a . 'a ctac -> 'a ctac -> 'a ctac =
  fun uu___1 ->
    fun uu___ ->
      (fun c1 ->
         fun c2 ->
           fun x ->
             let uu___ = c1 x in
             Obj.magic
               (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                  () () (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        let uu___1 = Obj.magic uu___1 in
                        match uu___1 with
                        | (x', flag) ->
                            (match flag with
                             | FStarC_Tactics_Types.Abort ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStarC_Class_Monad.return
                                         FStarC_Tactics_Monad.monad_tac ()
                                         (Obj.magic
                                            (x', FStarC_Tactics_Types.Abort))))
                             | FStarC_Tactics_Types.Skip ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStarC_Class_Monad.return
                                         FStarC_Tactics_Monad.monad_tac ()
                                         (Obj.magic
                                            (x', FStarC_Tactics_Types.Skip))))
                             | FStarC_Tactics_Types.Continue ->
                                 Obj.magic (Obj.repr (c2 x')))) uu___1)))
        uu___1 uu___
let (par_combine :
  (FStarC_Tactics_Types.ctrl_flag * FStarC_Tactics_Types.ctrl_flag) ->
    FStarC_Tactics_Types.ctrl_flag)
  =
  fun uu___ ->
    match uu___ with
    | (FStarC_Tactics_Types.Abort, uu___1) -> FStarC_Tactics_Types.Abort
    | (uu___1, FStarC_Tactics_Types.Abort) -> FStarC_Tactics_Types.Abort
    | (FStarC_Tactics_Types.Skip, uu___1) -> FStarC_Tactics_Types.Skip
    | (uu___1, FStarC_Tactics_Types.Skip) -> FStarC_Tactics_Types.Skip
    | (FStarC_Tactics_Types.Continue, FStarC_Tactics_Types.Continue) ->
        FStarC_Tactics_Types.Continue
let par_ctac : 'a 'b . 'a ctac -> 'b ctac -> ('a * 'b) ctac =
  fun uu___1 ->
    fun uu___ ->
      (fun cl ->
         fun cr ->
           fun uu___ ->
             match uu___ with
             | (x, y) ->
                 let uu___1 = cl x in
                 Obj.magic
                   (FStarC_Class_Monad.op_let_Bang
                      FStarC_Tactics_Monad.monad_tac () () (Obj.magic uu___1)
                      (fun uu___2 ->
                         (fun uu___2 ->
                            let uu___2 = Obj.magic uu___2 in
                            match uu___2 with
                            | (x1, flag) ->
                                (match flag with
                                 | FStarC_Tactics_Types.Abort ->
                                     Obj.magic
                                       (FStarC_Class_Monad.return
                                          FStarC_Tactics_Monad.monad_tac ()
                                          (Obj.magic
                                             ((x1, y),
                                               FStarC_Tactics_Types.Abort)))
                                 | fa ->
                                     let uu___3 = cr y in
                                     Obj.magic
                                       (FStarC_Class_Monad.op_let_Bang
                                          FStarC_Tactics_Monad.monad_tac ()
                                          () (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                let uu___4 = Obj.magic uu___4 in
                                                match uu___4 with
                                                | (y1, flag1) ->
                                                    (match flag1 with
                                                     | FStarC_Tactics_Types.Abort
                                                         ->
                                                         Obj.magic
                                                           (FStarC_Class_Monad.return
                                                              FStarC_Tactics_Monad.monad_tac
                                                              ()
                                                              (Obj.magic
                                                                 ((x1, y1),
                                                                   FStarC_Tactics_Types.Abort)))
                                                     | fb ->
                                                         Obj.magic
                                                           (FStarC_Class_Monad.return
                                                              FStarC_Tactics_Monad.monad_tac
                                                              ()
                                                              (Obj.magic
                                                                 ((x1, y1),
                                                                   (par_combine
                                                                    (fa, fb)))))))
                                               uu___4)))) uu___2))) uu___1
        uu___
let rec map_ctac : 'a . 'a ctac -> 'a Prims.list ctac =
  fun uu___ ->
    (fun c ->
       fun xs ->
         match xs with
         | [] ->
             Obj.magic
               (FStarC_Class_Monad.return FStarC_Tactics_Monad.monad_tac ()
                  (Obj.magic ([], FStarC_Tactics_Types.Continue)))
         | x::xs1 ->
             let uu___ =
               let uu___1 = let uu___2 = map_ctac c in par_ctac c uu___2 in
               uu___1 (x, xs1) in
             Obj.magic
               (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                  () () (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        let uu___1 = Obj.magic uu___1 in
                        match uu___1 with
                        | ((x1, xs2), flag) ->
                            Obj.magic
                              (FStarC_Class_Monad.return
                                 FStarC_Tactics_Monad.monad_tac ()
                                 (Obj.magic ((x1 :: xs2), flag)))) uu___1)))
      uu___
let ctac_id : 'a . 'a ctac =
  fun x ->
    Obj.magic
      (FStarC_Class_Monad.return FStarC_Tactics_Monad.monad_tac ()
         (Obj.magic (x, FStarC_Tactics_Types.Continue)))
let (ctac_args :
  FStarC_Syntax_Syntax.term ctac -> FStarC_Syntax_Syntax.args ctac) =
  fun c ->
    let uu___ = let uu___1 = ctac_id in par_ctac c uu___1 in map_ctac uu___
let (maybe_rewrite :
  FStarC_Tactics_Types.goal ->
    controller_ty ->
      rewriter_ty ->
        FStarC_TypeChecker_Env.env ->
          FStarC_Syntax_Syntax.term ->
            (FStarC_Syntax_Syntax.term * FStarC_Tactics_Types.ctrl_flag)
              FStarC_Tactics_Monad.tac)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g0 ->
               fun controller ->
                 fun rewriter ->
                   fun env ->
                     fun tm ->
                       let uu___ = controller tm in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Tactics_Monad.monad_tac () ()
                            (Obj.magic uu___)
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  let uu___1 = Obj.magic uu___1 in
                                  match uu___1 with
                                  | (rw, ctrl_flag) ->
                                      let uu___2 =
                                        if rw
                                        then
                                          Obj.magic
                                            (Obj.repr
                                               (do_rewrite g0 rewriter env tm))
                                        else
                                          Obj.magic
                                            (Obj.repr
                                               (FStarC_Class_Monad.return
                                                  FStarC_Tactics_Monad.monad_tac
                                                  () (Obj.magic tm))) in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_let_Bang
                                           FStarC_Tactics_Monad.monad_tac ()
                                           () (Obj.magic uu___2)
                                           (fun uu___3 ->
                                              (fun tm' ->
                                                 let tm' = Obj.magic tm' in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.return
                                                      FStarC_Tactics_Monad.monad_tac
                                                      ()
                                                      (Obj.magic
                                                         (tm', ctrl_flag))))
                                                uu___3))) uu___1))) uu___4
              uu___3 uu___2 uu___1 uu___
let rec (ctrl_fold_env :
  FStarC_Tactics_Types.goal ->
    FStarC_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStarC_TypeChecker_Env.env ->
            FStarC_Syntax_Syntax.term ->
              (FStarC_Syntax_Syntax.term * FStarC_Tactics_Types.ctrl_flag)
                FStarC_Tactics_Monad.tac)
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
              | FStarC_Tactics_Types.TopDown ->
                  let uu___ =
                    seq_ctac (maybe_rewrite g0 controller rewriter env)
                      (on_subterms g0 d controller rewriter env) in
                  uu___ tm
              | FStarC_Tactics_Types.BottomUp ->
                  let uu___ =
                    seq_ctac (on_subterms g0 d controller rewriter env)
                      (maybe_rewrite g0 controller rewriter env) in
                  uu___ tm
and (recurse_option_residual_comp :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.subst_elt Prims.list ->
      FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        (FStarC_TypeChecker_Env.env ->
           FStarC_Syntax_Syntax.term ->
             (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
               FStarC_Tactics_Types.ctrl_flag) FStarC_Tactics_Monad.tac)
          ->
          (FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
            * FStarC_Tactics_Types.ctrl_flag) FStarC_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun env ->
             fun retyping_subst ->
               fun rc_opt ->
                 fun recurse ->
                   match rc_opt with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (FStarC_Class_Monad.return
                            FStarC_Tactics_Monad.monad_tac ()
                            (Obj.magic
                               (FStar_Pervasives_Native.None,
                                 FStarC_Tactics_Types.Continue)))
                   | FStar_Pervasives_Native.Some rc ->
                       (match rc.FStarC_Syntax_Syntax.residual_typ with
                        | FStar_Pervasives_Native.None ->
                            Obj.magic
                              (FStarC_Class_Monad.return
                                 FStarC_Tactics_Monad.monad_tac ()
                                 (Obj.magic
                                    ((FStar_Pervasives_Native.Some rc),
                                      FStarC_Tactics_Types.Continue)))
                        | FStar_Pervasives_Native.Some t ->
                            let t1 =
                              FStarC_Syntax_Subst.subst retyping_subst t in
                            let uu___ = recurse env t1 in
                            Obj.magic
                              (FStarC_Class_Monad.op_let_Bang
                                 FStarC_Tactics_Monad.monad_tac () ()
                                 (Obj.magic uu___)
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       let uu___1 = Obj.magic uu___1 in
                                       match uu___1 with
                                       | (t2, flag) ->
                                           Obj.magic
                                             (FStarC_Class_Monad.return
                                                FStarC_Tactics_Monad.monad_tac
                                                ()
                                                (Obj.magic
                                                   ((FStar_Pervasives_Native.Some
                                                       {
                                                         FStarC_Syntax_Syntax.residual_effect
                                                           =
                                                           (rc.FStarC_Syntax_Syntax.residual_effect);
                                                         FStarC_Syntax_Syntax.residual_typ
                                                           =
                                                           (FStar_Pervasives_Native.Some
                                                              t2);
                                                         FStarC_Syntax_Syntax.residual_flags
                                                           =
                                                           (rc.FStarC_Syntax_Syntax.residual_flags)
                                                       }), flag)))) uu___1))))
            uu___3 uu___2 uu___1 uu___
and (on_subterms :
  FStarC_Tactics_Types.goal ->
    FStarC_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStarC_TypeChecker_Env.env ->
            FStarC_Syntax_Syntax.term ->
              (FStarC_Syntax_Syntax.term * FStarC_Tactics_Types.ctrl_flag)
                FStarC_Tactics_Monad.tac)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g0 ->
                 fun d ->
                   fun controller ->
                     fun rewriter ->
                       fun env ->
                         fun tm ->
                           let recurse env1 tm1 =
                             ctrl_fold_env g0 d controller rewriter env1 tm1 in
                           let rr = recurse env in
                           let rec descend_binders uu___8 uu___7 uu___6
                             uu___5 uu___4 uu___3 uu___2 uu___1 uu___ =
                             (fun orig ->
                                fun accum_binders ->
                                  fun retyping_subst ->
                                    fun accum_flag ->
                                      fun env1 ->
                                        fun bs ->
                                          fun t ->
                                            fun k ->
                                              fun rebuild ->
                                                match bs with
                                                | [] ->
                                                    let t1 =
                                                      FStarC_Syntax_Subst.subst
                                                        retyping_subst t in
                                                    let uu___ =
                                                      recurse env1 t1 in
                                                    Obj.magic
                                                      (FStarC_Class_Monad.op_let_Bang
                                                         FStarC_Tactics_Monad.monad_tac
                                                         () ()
                                                         (Obj.magic uu___)
                                                         (fun uu___1 ->
                                                            (fun uu___1 ->
                                                               let uu___1 =
                                                                 Obj.magic
                                                                   uu___1 in
                                                               match uu___1
                                                               with
                                                               | (t2, t_flag)
                                                                   ->
                                                                   (match t_flag
                                                                    with
                                                                    | 
                                                                    FStarC_Tactics_Types.Abort
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    ((orig.FStarC_Syntax_Syntax.n),
                                                                    t_flag)))
                                                                    | 
                                                                    uu___2 ->
                                                                    let uu___3
                                                                    =
                                                                    recurse_option_residual_comp
                                                                    env1
                                                                    retyping_subst
                                                                    k recurse in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___3)
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    let uu___4
                                                                    =
                                                                    Obj.magic
                                                                    uu___4 in
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    k_flag)
                                                                    ->
                                                                    let bs1 =
                                                                    FStarC_Compiler_List.rev
                                                                    accum_binders in
                                                                    let subst
                                                                    =
                                                                    FStarC_Syntax_Subst.closing_of_binders
                                                                    bs1 in
                                                                    let bs2 =
                                                                    FStarC_Syntax_Subst.close_binders
                                                                    bs1 in
                                                                    let t3 =
                                                                    FStarC_Syntax_Subst.subst
                                                                    subst t2 in
                                                                    let k2 =
                                                                    FStarC_Compiler_Util.map_option
                                                                    (FStarC_Syntax_Subst.subst_residual_comp
                                                                    subst) k1 in
                                                                    let uu___5
                                                                    =
                                                                    let uu___6
                                                                    =
                                                                    rebuild
                                                                    bs2 t3 k2 in
                                                                    (uu___6,
                                                                    (par_combine
                                                                    (accum_flag,
                                                                    (par_combine
                                                                    (t_flag,
                                                                    k_flag))))) in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___5)))
                                                                    uu___4))))
                                                              uu___1))
                                                | b::bs1 ->
                                                    let s =
                                                      FStarC_Syntax_Subst.subst
                                                        retyping_subst
                                                        (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                    let uu___ =
                                                      recurse env1 s in
                                                    Obj.magic
                                                      (FStarC_Class_Monad.op_let_Bang
                                                         FStarC_Tactics_Monad.monad_tac
                                                         () ()
                                                         (Obj.magic uu___)
                                                         (fun uu___1 ->
                                                            (fun uu___1 ->
                                                               let uu___1 =
                                                                 Obj.magic
                                                                   uu___1 in
                                                               match uu___1
                                                               with
                                                               | (s1, flag)
                                                                   ->
                                                                   (match flag
                                                                    with
                                                                    | 
                                                                    FStarC_Tactics_Types.Abort
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    ((orig.FStarC_Syntax_Syntax.n),
                                                                    flag))))
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let bv =
                                                                    let uu___3
                                                                    =
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    {
                                                                    FStarC_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___3.FStarC_Syntax_Syntax.ppname);
                                                                    FStarC_Syntax_Syntax.index
                                                                    =
                                                                    (uu___3.FStarC_Syntax_Syntax.index);
                                                                    FStarC_Syntax_Syntax.sort
                                                                    = s1
                                                                    } in
                                                                    let b1 =
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_qual);
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_positivity);
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_attrs)
                                                                    } in
                                                                    let env2
                                                                    =
                                                                    FStarC_TypeChecker_Env.push_binders
                                                                    env1 
                                                                    [b1] in
                                                                    let retyping_subst1
                                                                    =
                                                                    let uu___3
                                                                    =
                                                                    let uu___4
                                                                    =
                                                                    let uu___5
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    bv in
                                                                    (bv,
                                                                    uu___5) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___4 in
                                                                    uu___3 ::
                                                                    retyping_subst in
                                                                    descend_binders
                                                                    orig (b1
                                                                    ::
                                                                    accum_binders)
                                                                    retyping_subst1
                                                                    (par_combine
                                                                    (accum_flag,
                                                                    flag))
                                                                    env2 bs1
                                                                    t k
                                                                    rebuild))))
                                                              uu___1)))
                               uu___8 uu___7 uu___6 uu___5 uu___4 uu___3
                               uu___2 uu___1 uu___ in
                           let go uu___ =
                             (fun uu___ ->
                                let tm1 = FStarC_Syntax_Subst.compress tm in
                                match tm1.FStarC_Syntax_Syntax.n with
                                | FStarC_Syntax_Syntax.Tm_app
                                    { FStarC_Syntax_Syntax.hd = hd;
                                      FStarC_Syntax_Syntax.args = args;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___1 =
                                            let uu___2 =
                                              let uu___3 = ctac_args rr in
                                              par_ctac rr uu___3 in
                                            uu___2 (hd, args) in
                                          FStarC_Class_Monad.op_let_Bang
                                            FStarC_Tactics_Monad.monad_tac ()
                                            () (Obj.magic uu___1)
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  let uu___2 =
                                                    Obj.magic uu___2 in
                                                  match uu___2 with
                                                  | ((hd1, args1), flag) ->
                                                      Obj.magic
                                                        (FStarC_Class_Monad.return
                                                           FStarC_Tactics_Monad.monad_tac
                                                           ()
                                                           (Obj.magic
                                                              ((FStarC_Syntax_Syntax.Tm_app
                                                                  {
                                                                    FStarC_Syntax_Syntax.hd
                                                                    = hd1;
                                                                    FStarC_Syntax_Syntax.args
                                                                    = args1
                                                                  }), flag))))
                                                 uu___2)))
                                | FStarC_Syntax_Syntax.Tm_abs
                                    { FStarC_Syntax_Syntax.bs = bs;
                                      FStarC_Syntax_Syntax.body = t;
                                      FStarC_Syntax_Syntax.rc_opt = k;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___1 =
                                            FStarC_Syntax_Subst.open_term' bs
                                              t in
                                          match uu___1 with
                                          | (bs_orig, t1, subst) ->
                                              let k1 =
                                                FStarC_Compiler_Util.map_option
                                                  (FStarC_Syntax_Subst.subst_residual_comp
                                                     subst) k in
                                              descend_binders tm1 [] []
                                                FStarC_Tactics_Types.Continue
                                                env bs_orig t1 k1
                                                (fun bs1 ->
                                                   fun t2 ->
                                                     fun k2 ->
                                                       FStarC_Syntax_Syntax.Tm_abs
                                                         {
                                                           FStarC_Syntax_Syntax.bs
                                                             = bs1;
                                                           FStarC_Syntax_Syntax.body
                                                             = t2;
                                                           FStarC_Syntax_Syntax.rc_opt
                                                             = k2
                                                         })))
                                | FStarC_Syntax_Syntax.Tm_refine
                                    { FStarC_Syntax_Syntax.b = x;
                                      FStarC_Syntax_Syntax.phi = phi;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___1 =
                                            let uu___2 =
                                              let uu___3 =
                                                FStarC_Syntax_Syntax.mk_binder
                                                  x in
                                              [uu___3] in
                                            FStarC_Syntax_Subst.open_term
                                              uu___2 phi in
                                          match uu___1 with
                                          | (bs, phi1) ->
                                              descend_binders tm1 [] []
                                                FStarC_Tactics_Types.Continue
                                                env bs phi1
                                                FStar_Pervasives_Native.None
                                                (fun bs1 ->
                                                   fun phi2 ->
                                                     fun uu___2 ->
                                                       let x1 =
                                                         match bs1 with
                                                         | x2::[] ->
                                                             x2.FStarC_Syntax_Syntax.binder_bv
                                                         | uu___3 ->
                                                             failwith
                                                               "Impossible" in
                                                       FStarC_Syntax_Syntax.Tm_refine
                                                         {
                                                           FStarC_Syntax_Syntax.b
                                                             = x1;
                                                           FStarC_Syntax_Syntax.phi
                                                             = phi2
                                                         })))
                                | FStarC_Syntax_Syntax.Tm_arrow
                                    { FStarC_Syntax_Syntax.bs1 = bs;
                                      FStarC_Syntax_Syntax.comp = comp;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (match comp.FStarC_Syntax_Syntax.n
                                          with
                                          | FStarC_Syntax_Syntax.Total t ->
                                              Obj.repr
                                                (let uu___1 =
                                                   FStarC_Syntax_Subst.open_term
                                                     bs t in
                                                 match uu___1 with
                                                 | (bs_orig, t1) ->
                                                     descend_binders tm1 []
                                                       []
                                                       FStarC_Tactics_Types.Continue
                                                       env bs_orig t1
                                                       FStar_Pervasives_Native.None
                                                       (fun bs1 ->
                                                          fun t2 ->
                                                            fun uu___2 ->
                                                              FStarC_Syntax_Syntax.Tm_arrow
                                                                {
                                                                  FStarC_Syntax_Syntax.bs1
                                                                    = bs1;
                                                                  FStarC_Syntax_Syntax.comp
                                                                    =
                                                                    {
                                                                    FStarC_Syntax_Syntax.n
                                                                    =
                                                                    (FStarC_Syntax_Syntax.Total
                                                                    t2);
                                                                    FStarC_Syntax_Syntax.pos
                                                                    =
                                                                    (comp.FStarC_Syntax_Syntax.pos);
                                                                    FStarC_Syntax_Syntax.vars
                                                                    =
                                                                    (comp.FStarC_Syntax_Syntax.vars);
                                                                    FStarC_Syntax_Syntax.hash_code
                                                                    =
                                                                    (comp.FStarC_Syntax_Syntax.hash_code)
                                                                    }
                                                                }))
                                          | FStarC_Syntax_Syntax.GTotal t ->
                                              Obj.repr
                                                (let uu___1 =
                                                   FStarC_Syntax_Subst.open_term
                                                     bs t in
                                                 match uu___1 with
                                                 | (bs_orig, t1) ->
                                                     descend_binders tm1 []
                                                       []
                                                       FStarC_Tactics_Types.Continue
                                                       env bs_orig t1
                                                       FStar_Pervasives_Native.None
                                                       (fun bs1 ->
                                                          fun t2 ->
                                                            fun uu___2 ->
                                                              FStarC_Syntax_Syntax.Tm_arrow
                                                                {
                                                                  FStarC_Syntax_Syntax.bs1
                                                                    = bs1;
                                                                  FStarC_Syntax_Syntax.comp
                                                                    =
                                                                    {
                                                                    FStarC_Syntax_Syntax.n
                                                                    =
                                                                    (FStarC_Syntax_Syntax.GTotal
                                                                    t2);
                                                                    FStarC_Syntax_Syntax.pos
                                                                    =
                                                                    (comp.FStarC_Syntax_Syntax.pos);
                                                                    FStarC_Syntax_Syntax.vars
                                                                    =
                                                                    (comp.FStarC_Syntax_Syntax.vars);
                                                                    FStarC_Syntax_Syntax.hash_code
                                                                    =
                                                                    (comp.FStarC_Syntax_Syntax.hash_code)
                                                                    }
                                                                }))
                                          | uu___1 ->
                                              Obj.repr
                                                (FStarC_Class_Monad.return
                                                   FStarC_Tactics_Monad.monad_tac
                                                   ()
                                                   (Obj.magic
                                                      ((tm1.FStarC_Syntax_Syntax.n),
                                                        FStarC_Tactics_Types.Continue)))))
                                | FStarC_Syntax_Syntax.Tm_match
                                    { FStarC_Syntax_Syntax.scrutinee = hd;
                                      FStarC_Syntax_Syntax.ret_opt = asc_opt;
                                      FStarC_Syntax_Syntax.brs = brs;
                                      FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (let c_branch uu___1 =
                                            (fun br ->
                                               let uu___1 =
                                                 FStarC_Syntax_Subst.open_branch
                                                   br in
                                               match uu___1 with
                                               | (pat, w, e) ->
                                                   let bvs =
                                                     FStarC_Syntax_Syntax.pat_bvs
                                                       pat in
                                                   let uu___2 =
                                                     let uu___3 =
                                                       FStarC_TypeChecker_Env.push_bvs
                                                         env bvs in
                                                     recurse uu___3 e in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
                                                        () ()
                                                        (Obj.magic uu___2)
                                                        (fun uu___3 ->
                                                           (fun uu___3 ->
                                                              let uu___3 =
                                                                Obj.magic
                                                                  uu___3 in
                                                              match uu___3
                                                              with
                                                              | (e1, flag) ->
                                                                  let br1 =
                                                                    FStarC_Syntax_Subst.close_branch
                                                                    (pat, w,
                                                                    e1) in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.return
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    (br1,
                                                                    flag))))
                                                             uu___3))) uu___1 in
                                          let uu___1 =
                                            let uu___2 =
                                              let uu___3 = map_ctac c_branch in
                                              par_ctac rr uu___3 in
                                            uu___2 (hd, brs) in
                                          FStarC_Class_Monad.op_let_Bang
                                            FStarC_Tactics_Monad.monad_tac ()
                                            () (Obj.magic uu___1)
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  let uu___2 =
                                                    Obj.magic uu___2 in
                                                  match uu___2 with
                                                  | ((hd1, brs1), flag) ->
                                                      Obj.magic
                                                        (FStarC_Class_Monad.return
                                                           FStarC_Tactics_Monad.monad_tac
                                                           ()
                                                           (Obj.magic
                                                              ((FStarC_Syntax_Syntax.Tm_match
                                                                  {
                                                                    FStarC_Syntax_Syntax.scrutinee
                                                                    = hd1;
                                                                    FStarC_Syntax_Syntax.ret_opt
                                                                    = asc_opt;
                                                                    FStarC_Syntax_Syntax.brs
                                                                    = brs1;
                                                                    FStarC_Syntax_Syntax.rc_opt1
                                                                    = lopt
                                                                  }), flag))))
                                                 uu___2)))
                                | FStarC_Syntax_Syntax.Tm_let
                                    {
                                      FStarC_Syntax_Syntax.lbs =
                                        (false,
                                         {
                                           FStarC_Syntax_Syntax.lbname =
                                             FStar_Pervasives.Inl bv;
                                           FStarC_Syntax_Syntax.lbunivs =
                                             uu___1;
                                           FStarC_Syntax_Syntax.lbtyp =
                                             uu___2;
                                           FStarC_Syntax_Syntax.lbeff =
                                             uu___3;
                                           FStarC_Syntax_Syntax.lbdef = def;
                                           FStarC_Syntax_Syntax.lbattrs =
                                             uu___4;
                                           FStarC_Syntax_Syntax.lbpos =
                                             uu___5;_}::[]);
                                      FStarC_Syntax_Syntax.body1 = e;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (let lb =
                                            let uu___6 =
                                              let uu___7 =
                                                FStarC_Syntax_Subst.compress
                                                  tm1 in
                                              uu___7.FStarC_Syntax_Syntax.n in
                                            match uu___6 with
                                            | FStarC_Syntax_Syntax.Tm_let
                                                {
                                                  FStarC_Syntax_Syntax.lbs =
                                                    (false, lb1::[]);
                                                  FStarC_Syntax_Syntax.body1
                                                    = uu___7;_}
                                                -> lb1
                                            | uu___7 -> failwith "impossible" in
                                          let uu___6 =
                                            FStarC_Syntax_Subst.open_term_bv
                                              bv e in
                                          match uu___6 with
                                          | (bv1, e1) ->
                                              let uu___7 =
                                                let uu___8 =
                                                  let uu___9 =
                                                    let uu___10 =
                                                      FStarC_TypeChecker_Env.push_bv
                                                        env bv1 in
                                                    recurse uu___10 in
                                                  par_ctac rr uu___9 in
                                                uu___8
                                                  ((lb.FStarC_Syntax_Syntax.lbdef),
                                                    e1) in
                                              FStarC_Class_Monad.op_let_Bang
                                                FStarC_Tactics_Monad.monad_tac
                                                () () (Obj.magic uu___7)
                                                (fun uu___8 ->
                                                   (fun uu___8 ->
                                                      let uu___8 =
                                                        Obj.magic uu___8 in
                                                      match uu___8 with
                                                      | ((lbdef, e2), flag)
                                                          ->
                                                          let lb1 =
                                                            {
                                                              FStarC_Syntax_Syntax.lbname
                                                                =
                                                                (lb.FStarC_Syntax_Syntax.lbname);
                                                              FStarC_Syntax_Syntax.lbunivs
                                                                =
                                                                (lb.FStarC_Syntax_Syntax.lbunivs);
                                                              FStarC_Syntax_Syntax.lbtyp
                                                                =
                                                                (lb.FStarC_Syntax_Syntax.lbtyp);
                                                              FStarC_Syntax_Syntax.lbeff
                                                                =
                                                                (lb.FStarC_Syntax_Syntax.lbeff);
                                                              FStarC_Syntax_Syntax.lbdef
                                                                = lbdef;
                                                              FStarC_Syntax_Syntax.lbattrs
                                                                =
                                                                (lb.FStarC_Syntax_Syntax.lbattrs);
                                                              FStarC_Syntax_Syntax.lbpos
                                                                =
                                                                (lb.FStarC_Syntax_Syntax.lbpos)
                                                            } in
                                                          let e3 =
                                                            let uu___9 =
                                                              let uu___10 =
                                                                FStarC_Syntax_Syntax.mk_binder
                                                                  bv1 in
                                                              [uu___10] in
                                                            FStarC_Syntax_Subst.close
                                                              uu___9 e2 in
                                                          Obj.magic
                                                            (FStarC_Class_Monad.return
                                                               FStarC_Tactics_Monad.monad_tac
                                                               ()
                                                               (Obj.magic
                                                                  ((FStarC_Syntax_Syntax.Tm_let
                                                                    {
                                                                    FStarC_Syntax_Syntax.lbs
                                                                    =
                                                                    (false,
                                                                    [lb1]);
                                                                    FStarC_Syntax_Syntax.body1
                                                                    = e3
                                                                    }), flag))))
                                                     uu___8)))
                                | FStarC_Syntax_Syntax.Tm_let
                                    { FStarC_Syntax_Syntax.lbs = (true, lbs);
                                      FStarC_Syntax_Syntax.body1 = e;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (let c_lb uu___1 =
                                            (fun lb ->
                                               let uu___1 =
                                                 rr
                                                   lb.FStarC_Syntax_Syntax.lbdef in
                                               Obj.magic
                                                 (FStarC_Class_Monad.op_let_Bang
                                                    FStarC_Tactics_Monad.monad_tac
                                                    () () (Obj.magic uu___1)
                                                    (fun uu___2 ->
                                                       (fun uu___2 ->
                                                          let uu___2 =
                                                            Obj.magic uu___2 in
                                                          match uu___2 with
                                                          | (def, flag) ->
                                                              Obj.magic
                                                                (FStarC_Class_Monad.return
                                                                   FStarC_Tactics_Monad.monad_tac
                                                                   ()
                                                                   (Obj.magic
                                                                    ({
                                                                    FStarC_Syntax_Syntax.lbname
                                                                    =
                                                                    (lb.FStarC_Syntax_Syntax.lbname);
                                                                    FStarC_Syntax_Syntax.lbunivs
                                                                    =
                                                                    (lb.FStarC_Syntax_Syntax.lbunivs);
                                                                    FStarC_Syntax_Syntax.lbtyp
                                                                    =
                                                                    (lb.FStarC_Syntax_Syntax.lbtyp);
                                                                    FStarC_Syntax_Syntax.lbeff
                                                                    =
                                                                    (lb.FStarC_Syntax_Syntax.lbeff);
                                                                    FStarC_Syntax_Syntax.lbdef
                                                                    = def;
                                                                    FStarC_Syntax_Syntax.lbattrs
                                                                    =
                                                                    (lb.FStarC_Syntax_Syntax.lbattrs);
                                                                    FStarC_Syntax_Syntax.lbpos
                                                                    =
                                                                    (lb.FStarC_Syntax_Syntax.lbpos)
                                                                    }, flag))))
                                                         uu___2))) uu___1 in
                                          let uu___1 =
                                            FStarC_Syntax_Subst.open_let_rec
                                              lbs e in
                                          match uu___1 with
                                          | (lbs1, e1) ->
                                              let uu___2 =
                                                let uu___3 =
                                                  let uu___4 = map_ctac c_lb in
                                                  par_ctac uu___4 rr in
                                                uu___3 (lbs1, e1) in
                                              FStarC_Class_Monad.op_let_Bang
                                                FStarC_Tactics_Monad.monad_tac
                                                () () (Obj.magic uu___2)
                                                (fun uu___3 ->
                                                   (fun uu___3 ->
                                                      let uu___3 =
                                                        Obj.magic uu___3 in
                                                      match uu___3 with
                                                      | ((lbs2, e2), flag) ->
                                                          let uu___4 =
                                                            FStarC_Syntax_Subst.close_let_rec
                                                              lbs2 e2 in
                                                          (match uu___4 with
                                                           | (lbs3, e3) ->
                                                               Obj.magic
                                                                 (FStarC_Class_Monad.return
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (
                                                                    Obj.magic
                                                                    ((FStarC_Syntax_Syntax.Tm_let
                                                                    {
                                                                    FStarC_Syntax_Syntax.lbs
                                                                    =
                                                                    (true,
                                                                    lbs3);
                                                                    FStarC_Syntax_Syntax.body1
                                                                    = e3
                                                                    }), flag)))))
                                                     uu___3)))
                                | FStarC_Syntax_Syntax.Tm_ascribed
                                    { FStarC_Syntax_Syntax.tm = t;
                                      FStarC_Syntax_Syntax.asc = asc;
                                      FStarC_Syntax_Syntax.eff_opt = eff;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___1 = rr t in
                                          FStarC_Class_Monad.op_let_Bang
                                            FStarC_Tactics_Monad.monad_tac ()
                                            () (Obj.magic uu___1)
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  let uu___2 =
                                                    Obj.magic uu___2 in
                                                  match uu___2 with
                                                  | (t1, flag) ->
                                                      Obj.magic
                                                        (FStarC_Class_Monad.return
                                                           FStarC_Tactics_Monad.monad_tac
                                                           ()
                                                           (Obj.magic
                                                              ((FStarC_Syntax_Syntax.Tm_ascribed
                                                                  {
                                                                    FStarC_Syntax_Syntax.tm
                                                                    = t1;
                                                                    FStarC_Syntax_Syntax.asc
                                                                    = asc;
                                                                    FStarC_Syntax_Syntax.eff_opt
                                                                    = eff
                                                                  }), flag))))
                                                 uu___2)))
                                | FStarC_Syntax_Syntax.Tm_meta
                                    { FStarC_Syntax_Syntax.tm2 = t;
                                      FStarC_Syntax_Syntax.meta = m;_}
                                    ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___1 = rr t in
                                          FStarC_Class_Monad.op_let_Bang
                                            FStarC_Tactics_Monad.monad_tac ()
                                            () (Obj.magic uu___1)
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  let uu___2 =
                                                    Obj.magic uu___2 in
                                                  match uu___2 with
                                                  | (t1, flag) ->
                                                      Obj.magic
                                                        (FStarC_Class_Monad.return
                                                           FStarC_Tactics_Monad.monad_tac
                                                           ()
                                                           (Obj.magic
                                                              ((FStarC_Syntax_Syntax.Tm_meta
                                                                  {
                                                                    FStarC_Syntax_Syntax.tm2
                                                                    = t1;
                                                                    FStarC_Syntax_Syntax.meta
                                                                    = m
                                                                  }), flag))))
                                                 uu___2)))
                                | uu___1 ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStarC_Class_Monad.return
                                            FStarC_Tactics_Monad.monad_tac ()
                                            (Obj.magic
                                               ((tm1.FStarC_Syntax_Syntax.n),
                                                 FStarC_Tactics_Types.Continue)))))
                               uu___ in
                           let uu___ = go () in
                           Obj.magic
                             (FStarC_Class_Monad.op_let_Bang
                                FStarC_Tactics_Monad.monad_tac () ()
                                (Obj.magic uu___)
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      let uu___1 = Obj.magic uu___1 in
                                      match uu___1 with
                                      | (tmn', flag) ->
                                          Obj.magic
                                            (FStarC_Class_Monad.return
                                               FStarC_Tactics_Monad.monad_tac
                                               ()
                                               (Obj.magic
                                                  ({
                                                     FStarC_Syntax_Syntax.n =
                                                       tmn';
                                                     FStarC_Syntax_Syntax.pos
                                                       =
                                                       (tm.FStarC_Syntax_Syntax.pos);
                                                     FStarC_Syntax_Syntax.vars
                                                       =
                                                       (tm.FStarC_Syntax_Syntax.vars);
                                                     FStarC_Syntax_Syntax.hash_code
                                                       =
                                                       (tm.FStarC_Syntax_Syntax.hash_code)
                                                   }, flag)))) uu___1)))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (do_ctrl_rewrite :
  FStarC_Tactics_Types.goal ->
    FStarC_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStarC_TypeChecker_Env.env ->
            FStarC_Syntax_Syntax.term ->
              FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g0 ->
                 fun dir ->
                   fun controller ->
                     fun rewriter ->
                       fun env ->
                         fun tm ->
                           let uu___ =
                             ctrl_fold_env g0 dir controller rewriter env tm in
                           Obj.magic
                             (FStarC_Class_Monad.op_let_Bang
                                FStarC_Tactics_Monad.monad_tac () ()
                                (Obj.magic uu___)
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      let uu___1 = Obj.magic uu___1 in
                                      match uu___1 with
                                      | (tm', uu___2) ->
                                          Obj.magic
                                            (FStarC_Class_Monad.return
                                               FStarC_Tactics_Monad.monad_tac
                                               () (Obj.magic tm'))) uu___1)))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (ctrl_rewrite :
  FStarC_Tactics_Types.direction ->
    controller_ty -> rewriter_ty -> unit FStarC_Tactics_Monad.tac)
  =
  fun dir ->
    fun controller ->
      fun rewriter ->
        let uu___ =
          FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            (Obj.magic FStarC_Tactics_Monad.get)
            (fun uu___1 ->
               (fun ps ->
                  let ps = Obj.magic ps in
                  let uu___1 =
                    match ps.FStarC_Tactics_Types.goals with
                    | g::gs -> (g, gs)
                    | [] -> failwith "no goals" in
                  match uu___1 with
                  | (g, gs) ->
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Tactics_Monad.monad_tac () ()
                           FStarC_Tactics_Monad.dismiss_all
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 let uu___2 = Obj.magic uu___2 in
                                 let gt = FStarC_Tactics_Types.goal_type g in
                                 let uu___3 =
                                   FStarC_Tactics_Monad.if_verbose
                                     (fun uu___4 ->
                                        let uu___5 =
                                          FStarC_Class_Show.show
                                            FStarC_Syntax_Print.showable_term
                                            gt in
                                        FStarC_Compiler_Util.print1
                                          "ctrl_rewrite starting with %s\n"
                                          uu___5) in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Tactics_Monad.monad_tac () ()
                                      uu___3
                                      (fun uu___4 ->
                                         (fun uu___4 ->
                                            let uu___4 = Obj.magic uu___4 in
                                            let uu___5 =
                                              let uu___6 =
                                                FStarC_Tactics_Types.goal_env
                                                  g in
                                              do_ctrl_rewrite g dir
                                                controller rewriter uu___6 gt in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Tactics_Monad.monad_tac
                                                 () () (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    (fun gt' ->
                                                       let gt' =
                                                         Obj.magic gt' in
                                                       let uu___6 =
                                                         FStarC_Tactics_Monad.if_verbose
                                                           (fun uu___7 ->
                                                              let uu___8 =
                                                                FStarC_Class_Show.show
                                                                  FStarC_Syntax_Print.showable_term
                                                                  gt' in
                                                              FStarC_Compiler_Util.print1
                                                                "ctrl_rewrite seems to have succeded with %s\n"
                                                                uu___8) in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Tactics_Monad.monad_tac
                                                            () () uu___6
                                                            (fun uu___7 ->
                                                               (fun uu___7 ->
                                                                  let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    uu___7 in
                                                                  let uu___8
                                                                    =
                                                                    FStarC_Tactics_Monad.push_goals
                                                                    gs in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___8
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    uu___9 in
                                                                    let g1 =
                                                                    FStarC_Tactics_Monad.goal_with_type
                                                                    g gt' in
                                                                    Obj.magic
                                                                    (FStarC_Tactics_Monad.add_goals
                                                                    [g1]))
                                                                    uu___9)))
                                                                 uu___7)))
                                                      uu___6))) uu___4)))
                                uu___2))) uu___1) in
        FStarC_Tactics_Monad.wrap_err "ctrl_rewrite" uu___