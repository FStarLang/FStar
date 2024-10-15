open Prims
let (dbg_Core : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Core"
let (dbg_CoreEq : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "CoreEq"
let (dbg_RegisterGoal : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "RegisterGoal"
let (dbg_TacFail : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "TacFail"
let (goal_ctr : Prims.int FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref Prims.int_zero
let (get_goal_ctr : unit -> Prims.int) =
  fun uu___ -> FStarC_Compiler_Effect.op_Bang goal_ctr
let (incr_goal_ctr : unit -> Prims.int) =
  fun uu___ ->
    let v = FStarC_Compiler_Effect.op_Bang goal_ctr in
    FStarC_Compiler_Effect.op_Colon_Equals goal_ctr (v + Prims.int_one); v
let (is_goal_safe_as_well_typed : FStarC_Tactics_Types.goal -> Prims.bool) =
  fun g ->
    let uv = g.FStarC_Tactics_Types.goal_ctx_uvar in
    let all_deps_resolved =
      let uu___ = FStarC_Syntax_Util.ctx_uvar_typedness_deps uv in
      FStarC_Compiler_List.for_all
        (fun uv1 ->
           let uu___1 =
             FStarC_Syntax_Unionfind.find
               uv1.FStarC_Syntax_Syntax.ctx_uvar_head in
           match uu___1 with
           | FStar_Pervasives_Native.Some t ->
               let uu___2 = FStarC_Syntax_Free.uvars t in
               FStarC_Class_Setlike.is_empty ()
                 (Obj.magic
                    (FStarC_Compiler_FlatSet.setlike_flat_set
                       FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___2)
           | uu___2 -> false) uu___ in
    all_deps_resolved
let (register_goal : FStarC_Tactics_Types.goal -> unit) =
  fun g ->
    let uu___ =
      let uu___1 = FStarC_Options.compat_pre_core_should_register () in
      Prims.op_Negation uu___1 in
    if uu___
    then ()
    else
      (let env = FStarC_Tactics_Types.goal_env g in
       let uu___2 =
         env.FStarC_TypeChecker_Env.phase1 || (FStarC_Options.lax ()) in
       if uu___2
       then ()
       else
         (let uv = g.FStarC_Tactics_Types.goal_ctx_uvar in
          let i = FStarC_TypeChecker_Core.incr_goal_ctr () in
          let uu___4 =
            let uu___5 =
              FStarC_Syntax_Util.ctx_uvar_should_check
                g.FStarC_Tactics_Types.goal_ctx_uvar in
            FStarC_Syntax_Syntax.uu___is_Allow_untyped uu___5 in
          if uu___4
          then ()
          else
            (let env1 =
               {
                 FStarC_TypeChecker_Env.solver =
                   (env.FStarC_TypeChecker_Env.solver);
                 FStarC_TypeChecker_Env.range =
                   (env.FStarC_TypeChecker_Env.range);
                 FStarC_TypeChecker_Env.curmodule =
                   (env.FStarC_TypeChecker_Env.curmodule);
                 FStarC_TypeChecker_Env.gamma =
                   (uv.FStarC_Syntax_Syntax.ctx_uvar_gamma);
                 FStarC_TypeChecker_Env.gamma_sig =
                   (env.FStarC_TypeChecker_Env.gamma_sig);
                 FStarC_TypeChecker_Env.gamma_cache =
                   (env.FStarC_TypeChecker_Env.gamma_cache);
                 FStarC_TypeChecker_Env.modules =
                   (env.FStarC_TypeChecker_Env.modules);
                 FStarC_TypeChecker_Env.expected_typ =
                   (env.FStarC_TypeChecker_Env.expected_typ);
                 FStarC_TypeChecker_Env.sigtab =
                   (env.FStarC_TypeChecker_Env.sigtab);
                 FStarC_TypeChecker_Env.attrtab =
                   (env.FStarC_TypeChecker_Env.attrtab);
                 FStarC_TypeChecker_Env.instantiate_imp =
                   (env.FStarC_TypeChecker_Env.instantiate_imp);
                 FStarC_TypeChecker_Env.effects =
                   (env.FStarC_TypeChecker_Env.effects);
                 FStarC_TypeChecker_Env.generalize =
                   (env.FStarC_TypeChecker_Env.generalize);
                 FStarC_TypeChecker_Env.letrecs =
                   (env.FStarC_TypeChecker_Env.letrecs);
                 FStarC_TypeChecker_Env.top_level =
                   (env.FStarC_TypeChecker_Env.top_level);
                 FStarC_TypeChecker_Env.check_uvars =
                   (env.FStarC_TypeChecker_Env.check_uvars);
                 FStarC_TypeChecker_Env.use_eq_strict =
                   (env.FStarC_TypeChecker_Env.use_eq_strict);
                 FStarC_TypeChecker_Env.is_iface =
                   (env.FStarC_TypeChecker_Env.is_iface);
                 FStarC_TypeChecker_Env.admit =
                   (env.FStarC_TypeChecker_Env.admit);
                 FStarC_TypeChecker_Env.lax_universes =
                   (env.FStarC_TypeChecker_Env.lax_universes);
                 FStarC_TypeChecker_Env.phase1 =
                   (env.FStarC_TypeChecker_Env.phase1);
                 FStarC_TypeChecker_Env.failhard =
                   (env.FStarC_TypeChecker_Env.failhard);
                 FStarC_TypeChecker_Env.flychecking =
                   (env.FStarC_TypeChecker_Env.flychecking);
                 FStarC_TypeChecker_Env.uvar_subtyping =
                   (env.FStarC_TypeChecker_Env.uvar_subtyping);
                 FStarC_TypeChecker_Env.intactics =
                   (env.FStarC_TypeChecker_Env.intactics);
                 FStarC_TypeChecker_Env.nocoerce =
                   (env.FStarC_TypeChecker_Env.nocoerce);
                 FStarC_TypeChecker_Env.tc_term =
                   (env.FStarC_TypeChecker_Env.tc_term);
                 FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                   (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                 FStarC_TypeChecker_Env.universe_of =
                   (env.FStarC_TypeChecker_Env.universe_of);
                 FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                   (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                 FStarC_TypeChecker_Env.teq_nosmt_force =
                   (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                 FStarC_TypeChecker_Env.subtype_nosmt_force =
                   (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                 FStarC_TypeChecker_Env.qtbl_name_and_index =
                   (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                 FStarC_TypeChecker_Env.normalized_eff_names =
                   (env.FStarC_TypeChecker_Env.normalized_eff_names);
                 FStarC_TypeChecker_Env.fv_delta_depths =
                   (env.FStarC_TypeChecker_Env.fv_delta_depths);
                 FStarC_TypeChecker_Env.proof_ns =
                   (env.FStarC_TypeChecker_Env.proof_ns);
                 FStarC_TypeChecker_Env.synth_hook =
                   (env.FStarC_TypeChecker_Env.synth_hook);
                 FStarC_TypeChecker_Env.try_solve_implicits_hook =
                   (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                 FStarC_TypeChecker_Env.splice =
                   (env.FStarC_TypeChecker_Env.splice);
                 FStarC_TypeChecker_Env.mpreprocess =
                   (env.FStarC_TypeChecker_Env.mpreprocess);
                 FStarC_TypeChecker_Env.postprocess =
                   (env.FStarC_TypeChecker_Env.postprocess);
                 FStarC_TypeChecker_Env.identifier_info =
                   (env.FStarC_TypeChecker_Env.identifier_info);
                 FStarC_TypeChecker_Env.tc_hooks =
                   (env.FStarC_TypeChecker_Env.tc_hooks);
                 FStarC_TypeChecker_Env.dsenv =
                   (env.FStarC_TypeChecker_Env.dsenv);
                 FStarC_TypeChecker_Env.nbe =
                   (env.FStarC_TypeChecker_Env.nbe);
                 FStarC_TypeChecker_Env.strict_args_tab =
                   (env.FStarC_TypeChecker_Env.strict_args_tab);
                 FStarC_TypeChecker_Env.erasable_types_tab =
                   (env.FStarC_TypeChecker_Env.erasable_types_tab);
                 FStarC_TypeChecker_Env.enable_defer_to_tac =
                   (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                 FStarC_TypeChecker_Env.unif_allow_ref_guards =
                   (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                 FStarC_TypeChecker_Env.erase_erasable_args =
                   (env.FStarC_TypeChecker_Env.erase_erasable_args);
                 FStarC_TypeChecker_Env.core_check =
                   (env.FStarC_TypeChecker_Env.core_check);
                 FStarC_TypeChecker_Env.missing_decl =
                   (env.FStarC_TypeChecker_Env.missing_decl)
               } in
             (let uu___7 = FStarC_Compiler_Effect.op_Bang dbg_CoreEq in
              if uu___7
              then
                let uu___8 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                FStarC_Compiler_Util.print1 "(%s) Registering goal\n" uu___8
              else ());
             (let should_register = is_goal_safe_as_well_typed g in
              if Prims.op_Negation should_register
              then
                let uu___8 =
                  (FStarC_Compiler_Effect.op_Bang dbg_Core) ||
                    (FStarC_Compiler_Effect.op_Bang dbg_RegisterGoal) in
                (if uu___8
                 then
                   let uu___9 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                   FStarC_Compiler_Util.print1
                     "(%s) Not registering goal since it has unresolved uvar deps\n"
                     uu___9
                 else ())
              else
                ((let uu___9 =
                    (FStarC_Compiler_Effect.op_Bang dbg_Core) ||
                      (FStarC_Compiler_Effect.op_Bang dbg_RegisterGoal) in
                  if uu___9
                  then
                    let uu___10 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                    let uu___11 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_ctxu uv in
                    FStarC_Compiler_Util.print2
                      "(%s) Registering goal for %s\n" uu___10 uu___11
                  else ());
                 (let goal_ty = FStarC_Syntax_Util.ctx_uvar_typ uv in
                  let uu___9 =
                    FStarC_TypeChecker_Core.compute_term_type_handle_guards
                      env1 goal_ty (fun uu___10 -> fun uu___11 -> true) in
                  match uu___9 with
                  | FStar_Pervasives.Inl uu___10 -> ()
                  | FStar_Pervasives.Inr err ->
                      let msg =
                        let uu___10 =
                          let uu___11 = FStarC_Syntax_Util.ctx_uvar_typ uv in
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_term uu___11 in
                        let uu___11 =
                          FStarC_TypeChecker_Core.print_error_short err in
                        FStarC_Compiler_Util.format2
                          "Failed to check initial tactic goal %s because %s"
                          uu___10 uu___11 in
                      FStarC_Errors.log_issue
                        FStarC_Class_HasRange.hasRange_range
                        uv.FStarC_Syntax_Syntax.ctx_uvar_range
                        FStarC_Errors_Codes.Warning_FailedToCheckInitialTacticGoal
                        ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic msg)))))))
type 'a tac =
  {
  tac_f: FStarC_Tactics_Types.proofstate -> 'a FStarC_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStarC_Tactics_Types.proofstate -> 'a FStarC_Tactics_Result.__result
  = fun projectee -> match projectee with | { tac_f;_} -> tac_f
let mk_tac :
  'a .
    (FStarC_Tactics_Types.proofstate -> 'a FStarC_Tactics_Result.__result) ->
      'a tac
  = fun f -> { tac_f = f }
let run :
  'a .
    'a tac ->
      FStarC_Tactics_Types.proofstate -> 'a FStarC_Tactics_Result.__result
  = fun t -> fun ps -> t.tac_f ps
let run_safe :
  'a .
    'a tac ->
      FStarC_Tactics_Types.proofstate -> 'a FStarC_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      let uu___ = FStarC_Options.tactics_failhard () in
      if uu___
      then run t ps
      else
        (try (fun uu___2 -> match () with | () -> run t ps) ()
         with | uu___2 -> FStarC_Tactics_Result.Failed (uu___2, ps))
let ret : 'a . 'a -> 'a tac =
  fun x -> mk_tac (fun ps -> FStarC_Tactics_Result.Success (x, ps))
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1 ->
    fun t2 ->
      mk_tac
        (fun ps ->
           let uu___ = run t1 ps in
           match uu___ with
           | FStarC_Tactics_Result.Success (a1, q) ->
               let uu___1 = t2 a1 in run uu___1 q
           | FStarC_Tactics_Result.Failed (msg, q) ->
               FStarC_Tactics_Result.Failed (msg, q))
let (monad_tac : unit tac FStarC_Class_Monad.monad) =
  {
    FStarC_Class_Monad.return =
      (fun uu___1 -> fun uu___ -> (fun uu___ -> Obj.magic ret) uu___1 uu___);
    FStarC_Class_Monad.op_let_Bang =
      (fun uu___3 ->
         fun uu___2 ->
           fun uu___1 ->
             fun uu___ ->
               (fun uu___1 -> fun uu___ -> Obj.magic bind) uu___3 uu___2
                 uu___1 uu___)
  }
let (set : FStarC_Tactics_Types.proofstate -> unit tac) =
  fun ps -> mk_tac (fun uu___ -> FStarC_Tactics_Result.Success ((), ps))
let (get : FStarC_Tactics_Types.proofstate tac) =
  mk_tac (fun ps -> FStarC_Tactics_Result.Success (ps, ps))
let traise : 'a . Prims.exn -> 'a tac =
  fun e -> mk_tac (fun ps -> FStarC_Tactics_Result.Failed (e, ps))
let (do_log : FStarC_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps ->
    fun f -> if ps.FStarC_Tactics_Types.tac_verb_dbg then f () else ()
let (log : (unit -> unit) -> unit tac) =
  fun f ->
    mk_tac (fun ps -> do_log ps f; FStarC_Tactics_Result.Success ((), ps))
let fail_doc : 'a . FStarC_Errors_Msg.error_message -> 'a tac =
  fun msg ->
    mk_tac
      (fun ps ->
         (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_TacFail in
          if uu___1
          then
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_Compiler_List.hd msg in
                FStarC_Errors_Msg.renderdoc uu___4 in
              Prims.strcat "TACTIC FAILING: " uu___3 in
            FStarC_Tactics_Printing.do_dump_proofstate ps uu___2
          else ());
         FStarC_Tactics_Result.Failed
           ((FStarC_Tactics_Common.TacticFailure
               (msg, FStar_Pervasives_Native.None)), ps))
let fail : 'a . Prims.string -> 'a tac =
  fun msg ->
    let uu___ = let uu___1 = FStarC_Errors_Msg.text msg in [uu___1] in
    fail_doc uu___
let catch : 'a . 'a tac -> (Prims.exn, 'a) FStar_Pervasives.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let idtable =
           FStarC_Compiler_Effect.op_Bang
             (ps.FStarC_Tactics_Types.main_context).FStarC_TypeChecker_Env.identifier_info in
         let tx = FStarC_Syntax_Unionfind.new_transaction () in
         let uu___ = run t ps in
         match uu___ with
         | FStarC_Tactics_Result.Success (a1, q) ->
             (FStarC_Syntax_Unionfind.commit tx;
              FStarC_Tactics_Result.Success ((FStar_Pervasives.Inr a1), q))
         | FStarC_Tactics_Result.Failed (m, q) ->
             (FStarC_Syntax_Unionfind.rollback tx;
              FStarC_Compiler_Effect.op_Colon_Equals
                (ps.FStarC_Tactics_Types.main_context).FStarC_TypeChecker_Env.identifier_info
                idtable;
              (let ps1 =
                 {
                   FStarC_Tactics_Types.main_context =
                     (ps.FStarC_Tactics_Types.main_context);
                   FStarC_Tactics_Types.all_implicits =
                     (ps.FStarC_Tactics_Types.all_implicits);
                   FStarC_Tactics_Types.goals =
                     (ps.FStarC_Tactics_Types.goals);
                   FStarC_Tactics_Types.smt_goals =
                     (ps.FStarC_Tactics_Types.smt_goals);
                   FStarC_Tactics_Types.depth =
                     (ps.FStarC_Tactics_Types.depth);
                   FStarC_Tactics_Types.__dump =
                     (ps.FStarC_Tactics_Types.__dump);
                   FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
                   FStarC_Tactics_Types.entry_range =
                     (ps.FStarC_Tactics_Types.entry_range);
                   FStarC_Tactics_Types.guard_policy =
                     (ps.FStarC_Tactics_Types.guard_policy);
                   FStarC_Tactics_Types.freshness =
                     (q.FStarC_Tactics_Types.freshness);
                   FStarC_Tactics_Types.tac_verb_dbg =
                     (ps.FStarC_Tactics_Types.tac_verb_dbg);
                   FStarC_Tactics_Types.local_state =
                     (ps.FStarC_Tactics_Types.local_state);
                   FStarC_Tactics_Types.urgency =
                     (ps.FStarC_Tactics_Types.urgency);
                   FStarC_Tactics_Types.dump_on_failure =
                     (ps.FStarC_Tactics_Types.dump_on_failure)
                 } in
               FStarC_Tactics_Result.Success ((FStar_Pervasives.Inl m), ps1))))
let recover : 'a . 'a tac -> (Prims.exn, 'a) FStar_Pervasives.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let uu___ = run t ps in
         match uu___ with
         | FStarC_Tactics_Result.Success (a1, q) ->
             FStarC_Tactics_Result.Success ((FStar_Pervasives.Inr a1), q)
         | FStarC_Tactics_Result.Failed (m, q) ->
             FStarC_Tactics_Result.Success ((FStar_Pervasives.Inl m), q))
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t ->
    let uu___ = catch t in
    bind uu___
      (fun r ->
         match r with
         | FStar_Pervasives.Inr v -> ret (FStar_Pervasives_Native.Some v)
         | FStar_Pervasives.Inl uu___1 -> ret FStar_Pervasives_Native.None)
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t ->
    mk_tac
      (fun ps ->
         try
           (fun uu___ ->
              match () with | () -> let uu___1 = trytac t in run uu___1 ps)
             ()
         with
         | FStarC_Errors.Error (uu___1, msg, uu___2, uu___3) ->
             (do_log ps
                (fun uu___5 ->
                   let uu___6 = FStarC_Errors_Msg.rendermsg msg in
                   FStarC_Compiler_Util.print1 "trytac_exn error: (%s)"
                     uu___6);
              FStarC_Tactics_Result.Success
                (FStar_Pervasives_Native.None, ps)))
let rec iter_tac : 'a . ('a -> unit tac) -> 'a Prims.list -> unit tac =
  fun f ->
    fun l ->
      match l with
      | [] -> ret ()
      | hd::tl ->
          let uu___ = f hd in
          FStarC_Class_Monad.op_let_Bang monad_tac () () uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in Obj.magic (iter_tac f tl))
                 uu___1)
exception Bad of Prims.string 
let (uu___is_Bad : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Bad uu___ -> true | uu___ -> false
let (__proj__Bad__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Bad uu___ -> uu___
let (nwarn : Prims.int FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref Prims.int_zero
let (check_valid_goal : FStarC_Tactics_Types.goal -> unit) =
  fun g ->
    let uu___ = FStarC_Options.defensive () in
    if uu___
    then
      try
        (fun uu___1 ->
           match () with
           | () ->
               let env = FStarC_Tactics_Types.goal_env g in
               ((let uu___3 =
                   let uu___4 =
                     let uu___5 = FStarC_Tactics_Types.goal_witness g in
                     FStarC_TypeChecker_Env.closed env uu___5 in
                   Prims.op_Negation uu___4 in
                 if uu___3
                 then FStarC_Compiler_Effect.raise (Bad "witness")
                 else ());
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStarC_Tactics_Types.goal_type g in
                     FStarC_TypeChecker_Env.closed env uu___6 in
                   Prims.op_Negation uu___5 in
                 if uu___4
                 then FStarC_Compiler_Effect.raise (Bad "goal type")
                 else ());
                (let rec aux e =
                   let uu___4 = FStarC_TypeChecker_Env.pop_bv e in
                   match uu___4 with
                   | FStar_Pervasives_Native.None -> ()
                   | FStar_Pervasives_Native.Some (bv, e1) ->
                       ((let uu___6 =
                           let uu___7 =
                             FStarC_TypeChecker_Env.closed e1
                               bv.FStarC_Syntax_Syntax.sort in
                           Prims.op_Negation uu___7 in
                         if uu___6
                         then
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_bv bv in
                               Prims.strcat "bv: " uu___9 in
                             Bad uu___8 in
                           FStarC_Compiler_Effect.raise uu___7
                         else ());
                        aux e1) in
                 aux env))) ()
      with
      | Bad culprit ->
          let uu___2 =
            let uu___3 = FStarC_Compiler_Effect.op_Bang nwarn in
            uu___3 < (Prims.of_int (5)) in
          (if uu___2
           then
             ((let uu___4 = FStarC_Tactics_Types.goal_type g in
               let uu___5 =
                 let uu___6 =
                   FStarC_Tactics_Printing.goal_to_string_verbose g in
                 FStarC_Compiler_Util.format2
                   "The following goal is ill-formed (%s). Keeping calm and carrying on...\n<%s>\n\n"
                   culprit uu___6 in
               FStarC_Errors.log_issue
                 (FStarC_Syntax_Syntax.has_range_syntax ()) uu___4
                 FStarC_Errors_Codes.Warning_IllFormedGoal ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                 (Obj.magic uu___5));
              (let uu___4 =
                 let uu___5 = FStarC_Compiler_Effect.op_Bang nwarn in
                 uu___5 + Prims.int_one in
               FStarC_Compiler_Effect.op_Colon_Equals nwarn uu___4))
           else ())
    else ()
let (check_valid_goals : FStarC_Tactics_Types.goal Prims.list -> unit) =
  fun gs ->
    let uu___ = FStarC_Options.defensive () in
    if uu___ then FStarC_Compiler_List.iter check_valid_goal gs else ()
let (set_goals : FStarC_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals = gs;
             FStarC_Tactics_Types.smt_goals =
               (ps.FStarC_Tactics_Types.smt_goals);
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy =
               (ps.FStarC_Tactics_Types.guard_policy);
             FStarC_Tactics_Types.freshness =
               (ps.FStarC_Tactics_Types.freshness);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           })
let (set_smt_goals : FStarC_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
             FStarC_Tactics_Types.smt_goals = gs;
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy =
               (ps.FStarC_Tactics_Types.guard_policy);
             FStarC_Tactics_Types.freshness =
               (ps.FStarC_Tactics_Types.freshness);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           })
let (cur_goals : FStarC_Tactics_Types.goal Prims.list tac) =
  bind get (fun ps -> ret ps.FStarC_Tactics_Types.goals)
let (cur_goal_maybe_solved : FStarC_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___ ->
       match uu___ with | [] -> fail "No more goals" | hd::tl -> ret hd)
let (cur_goal : FStarC_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___ ->
       match uu___ with
       | [] -> fail "No more goals"
       | hd::tl ->
           let uu___1 = FStarC_Tactics_Types.check_goal_solved' hd in
           (match uu___1 with
            | FStar_Pervasives_Native.None -> ret hd
            | FStar_Pervasives_Native.Some t ->
                ((let uu___3 =
                    FStarC_Tactics_Printing.goal_to_string_verbose hd in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t in
                  FStarC_Compiler_Util.print2
                    "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                    uu___3 uu___4);
                 ret hd)))
let (remove_solved_goals : unit tac) =
  bind cur_goals
    (fun gs ->
       let gs1 =
         FStarC_Compiler_List.filter
           (fun g ->
              let uu___ = FStarC_Tactics_Types.check_goal_solved g in
              Prims.op_Negation uu___) gs in
       set_goals gs1)
let (dismiss_all : unit tac) = set_goals []
let (dismiss : unit tac) =
  bind get
    (fun ps ->
       let uu___ =
         let uu___1 = FStarC_Compiler_List.tl ps.FStarC_Tactics_Types.goals in
         {
           FStarC_Tactics_Types.main_context =
             (ps.FStarC_Tactics_Types.main_context);
           FStarC_Tactics_Types.all_implicits =
             (ps.FStarC_Tactics_Types.all_implicits);
           FStarC_Tactics_Types.goals = uu___1;
           FStarC_Tactics_Types.smt_goals =
             (ps.FStarC_Tactics_Types.smt_goals);
           FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
           FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
           FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
           FStarC_Tactics_Types.entry_range =
             (ps.FStarC_Tactics_Types.entry_range);
           FStarC_Tactics_Types.guard_policy =
             (ps.FStarC_Tactics_Types.guard_policy);
           FStarC_Tactics_Types.freshness =
             (ps.FStarC_Tactics_Types.freshness);
           FStarC_Tactics_Types.tac_verb_dbg =
             (ps.FStarC_Tactics_Types.tac_verb_dbg);
           FStarC_Tactics_Types.local_state =
             (ps.FStarC_Tactics_Types.local_state);
           FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
           FStarC_Tactics_Types.dump_on_failure =
             (ps.FStarC_Tactics_Types.dump_on_failure)
         } in
       set uu___)
let (replace_cur : FStarC_Tactics_Types.goal -> unit tac) =
  fun g ->
    bind get
      (fun ps ->
         check_valid_goal g;
         (let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_Compiler_List.tl ps.FStarC_Tactics_Types.goals in
              g :: uu___3 in
            {
              FStarC_Tactics_Types.main_context =
                (ps.FStarC_Tactics_Types.main_context);
              FStarC_Tactics_Types.all_implicits =
                (ps.FStarC_Tactics_Types.all_implicits);
              FStarC_Tactics_Types.goals = uu___2;
              FStarC_Tactics_Types.smt_goals =
                (ps.FStarC_Tactics_Types.smt_goals);
              FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
              FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
              FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
              FStarC_Tactics_Types.entry_range =
                (ps.FStarC_Tactics_Types.entry_range);
              FStarC_Tactics_Types.guard_policy =
                (ps.FStarC_Tactics_Types.guard_policy);
              FStarC_Tactics_Types.freshness =
                (ps.FStarC_Tactics_Types.freshness);
              FStarC_Tactics_Types.tac_verb_dbg =
                (ps.FStarC_Tactics_Types.tac_verb_dbg);
              FStarC_Tactics_Types.local_state =
                (ps.FStarC_Tactics_Types.local_state);
              FStarC_Tactics_Types.urgency =
                (ps.FStarC_Tactics_Types.urgency);
              FStarC_Tactics_Types.dump_on_failure =
                (ps.FStarC_Tactics_Types.dump_on_failure)
            } in
          set uu___1))
let (getopts : FStarC_Options.optionstate tac) =
  let uu___ = trytac cur_goal_maybe_solved in
  bind uu___
    (fun uu___1 ->
       match uu___1 with
       | FStar_Pervasives_Native.Some g -> ret g.FStarC_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu___2 = FStarC_Options.peek () in ret uu___2)
let (add_goals : FStarC_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals =
               (FStarC_Compiler_List.op_At gs ps.FStarC_Tactics_Types.goals);
             FStarC_Tactics_Types.smt_goals =
               (ps.FStarC_Tactics_Types.smt_goals);
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy =
               (ps.FStarC_Tactics_Types.guard_policy);
             FStarC_Tactics_Types.freshness =
               (ps.FStarC_Tactics_Types.freshness);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           })
let (add_smt_goals : FStarC_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
             FStarC_Tactics_Types.smt_goals =
               (FStarC_Compiler_List.op_At gs
                  ps.FStarC_Tactics_Types.smt_goals);
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy =
               (ps.FStarC_Tactics_Types.guard_policy);
             FStarC_Tactics_Types.freshness =
               (ps.FStarC_Tactics_Types.freshness);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           })
let (push_goals : FStarC_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals =
               (FStarC_Compiler_List.op_At ps.FStarC_Tactics_Types.goals gs);
             FStarC_Tactics_Types.smt_goals =
               (ps.FStarC_Tactics_Types.smt_goals);
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy =
               (ps.FStarC_Tactics_Types.guard_policy);
             FStarC_Tactics_Types.freshness =
               (ps.FStarC_Tactics_Types.freshness);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           })
let (push_smt_goals : FStarC_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
             FStarC_Tactics_Types.smt_goals =
               (FStarC_Compiler_List.op_At ps.FStarC_Tactics_Types.smt_goals
                  gs);
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy =
               (ps.FStarC_Tactics_Types.guard_policy);
             FStarC_Tactics_Types.freshness =
               (ps.FStarC_Tactics_Types.freshness);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           })
let (add_implicits : FStarC_TypeChecker_Env.implicits -> unit tac) =
  fun i ->
    bind get
      (fun ps ->
         set
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (FStarC_Compiler_List.op_At i
                  ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
             FStarC_Tactics_Types.smt_goals =
               (ps.FStarC_Tactics_Types.smt_goals);
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy =
               (ps.FStarC_Tactics_Types.guard_policy);
             FStarC_Tactics_Types.freshness =
               (ps.FStarC_Tactics_Types.freshness);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           })
let (new_uvar :
  Prims.string ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStarC_Syntax_Syntax.ctx_uvar Prims.list ->
            FStarC_Compiler_Range_Type.range ->
              (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason ->
    fun env ->
      fun typ ->
        fun sc_opt ->
          fun uvar_typedness_deps ->
            fun rng ->
              let should_check =
                match sc_opt with
                | FStar_Pervasives_Native.Some sc -> sc
                | uu___ -> FStarC_Syntax_Syntax.Strict in
              let uu___ =
                FStarC_TypeChecker_Env.new_tac_implicit_var reason rng env
                  typ should_check uvar_typedness_deps
                  FStar_Pervasives_Native.None false in
              match uu___ with
              | (u, ctx_uvar, g_u) ->
                  let uu___1 =
                    let uu___2 =
                      FStarC_Class_Listlike.to_list
                        (FStarC_Compiler_CList.listlike_clist ())
                        g_u.FStarC_TypeChecker_Common.implicits in
                    add_implicits uu___2 in
                  bind uu___1
                    (fun uu___2 ->
                       ret (u, (FStar_Pervasives_Native.fst ctx_uvar)))
let (mk_irrelevant_goal :
  Prims.string ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStarC_Compiler_Range_Type.range ->
            FStarC_Options.optionstate ->
              Prims.string -> FStarC_Tactics_Types.goal tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun sc_opt ->
          fun rng ->
            fun opts ->
              fun label ->
                let typ =
                  let uu___ = env.FStarC_TypeChecker_Env.universe_of env phi in
                  FStarC_Syntax_Util.mk_squash uu___ phi in
                let uu___ = new_uvar reason env typ sc_opt [] rng in
                bind uu___
                  (fun uu___1 ->
                     match uu___1 with
                     | (uu___2, ctx_uvar) ->
                         let goal =
                           FStarC_Tactics_Types.mk_goal env ctx_uvar opts
                             false label in
                         ret goal)
let (add_irrelevant_goal' :
  Prims.string ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStarC_Compiler_Range_Type.range ->
            FStarC_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun sc_opt ->
          fun rng ->
            fun opts ->
              fun label ->
                let uu___ =
                  mk_irrelevant_goal reason env phi sc_opt rng opts label in
                bind uu___ (fun goal -> add_goals [goal])
let (add_irrelevant_goal :
  FStarC_Tactics_Types.goal ->
    Prims.string ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_Syntax_Syntax.should_check_uvar
            FStar_Pervasives_Native.option -> unit tac)
  =
  fun base_goal ->
    fun reason ->
      fun env ->
        fun phi ->
          fun sc_opt ->
            add_irrelevant_goal' reason env phi sc_opt
              (base_goal.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_range
              base_goal.FStarC_Tactics_Types.opts
              base_goal.FStarC_Tactics_Types.label
let (goal_of_guard :
  Prims.string ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStarC_Compiler_Range_Type.range -> FStarC_Tactics_Types.goal tac)
  =
  fun reason ->
    fun e ->
      fun f ->
        fun sc_opt ->
          fun rng ->
            bind getopts
              (fun opts ->
                 let uu___ = mk_irrelevant_goal reason e f sc_opt rng opts "" in
                 bind uu___
                   (fun goal ->
                      let goal1 =
                        {
                          FStarC_Tactics_Types.goal_main_env =
                            (goal.FStarC_Tactics_Types.goal_main_env);
                          FStarC_Tactics_Types.goal_ctx_uvar =
                            (goal.FStarC_Tactics_Types.goal_ctx_uvar);
                          FStarC_Tactics_Types.opts =
                            (goal.FStarC_Tactics_Types.opts);
                          FStarC_Tactics_Types.is_guard = true;
                          FStarC_Tactics_Types.label =
                            (goal.FStarC_Tactics_Types.label)
                        } in
                      ret goal1))
let wrap_err_doc : 'a . FStarC_Errors_Msg.error_message -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      mk_tac
        (fun ps ->
           let uu___ = run t ps in
           match uu___ with
           | FStarC_Tactics_Result.Success (a1, q) ->
               FStarC_Tactics_Result.Success (a1, q)
           | FStarC_Tactics_Result.Failed
               (FStarC_Tactics_Common.TacticFailure (msg, r), q) ->
               FStarC_Tactics_Result.Failed
                 ((FStarC_Tactics_Common.TacticFailure
                     ((FStarC_Compiler_List.op_At pref msg), r)), q)
           | FStarC_Tactics_Result.Failed (e, q) ->
               FStarC_Tactics_Result.Failed (e, q))
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      let uu___ =
        let uu___1 =
          FStarC_Errors_Msg.text
            (Prims.strcat "'" (Prims.strcat pref "' failed")) in
        [uu___1] in
      wrap_err_doc uu___ t
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun cont ->
           let uu___ = log f in
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang monad_tac () () uu___
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in Obj.magic (cont ()))
                     uu___1))) uu___1 uu___
let (if_verbose_tac : (unit -> unit tac) -> unit tac) =
  fun f ->
    FStarC_Class_Monad.op_let_Bang monad_tac () () (Obj.magic get)
      (fun uu___ ->
         (fun ps ->
            let ps = Obj.magic ps in
            if ps.FStarC_Tactics_Types.tac_verb_dbg
            then Obj.magic (f ())
            else Obj.magic (ret ())) uu___)
let (if_verbose : (unit -> unit) -> unit tac) =
  fun f -> if_verbose_tac (fun uu___ -> f (); ret ())
let (compress_implicits : unit tac) =
  bind get
    (fun ps ->
       let imps = ps.FStarC_Tactics_Types.all_implicits in
       let g =
         let uu___ =
           FStarC_Class_Listlike.from_list
             (FStarC_Compiler_CList.listlike_clist ()) imps in
         {
           FStarC_TypeChecker_Common.guard_f =
             (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.guard_f);
           FStarC_TypeChecker_Common.deferred_to_tac =
             (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.deferred_to_tac);
           FStarC_TypeChecker_Common.deferred =
             (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.deferred);
           FStarC_TypeChecker_Common.univ_ineqs =
             (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.univ_ineqs);
           FStarC_TypeChecker_Common.implicits = uu___
         } in
       let imps1 =
         FStarC_TypeChecker_Rel.resolve_implicits_tac
           ps.FStarC_Tactics_Types.main_context g in
       let ps' =
         let uu___ =
           FStarC_Compiler_List.map FStar_Pervasives_Native.fst imps1 in
         {
           FStarC_Tactics_Types.main_context =
             (ps.FStarC_Tactics_Types.main_context);
           FStarC_Tactics_Types.all_implicits = uu___;
           FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
           FStarC_Tactics_Types.smt_goals =
             (ps.FStarC_Tactics_Types.smt_goals);
           FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
           FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
           FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
           FStarC_Tactics_Types.entry_range =
             (ps.FStarC_Tactics_Types.entry_range);
           FStarC_Tactics_Types.guard_policy =
             (ps.FStarC_Tactics_Types.guard_policy);
           FStarC_Tactics_Types.freshness =
             (ps.FStarC_Tactics_Types.freshness);
           FStarC_Tactics_Types.tac_verb_dbg =
             (ps.FStarC_Tactics_Types.tac_verb_dbg);
           FStarC_Tactics_Types.local_state =
             (ps.FStarC_Tactics_Types.local_state);
           FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
           FStarC_Tactics_Types.dump_on_failure =
             (ps.FStarC_Tactics_Types.dump_on_failure)
         } in
       set ps')
let (get_phi :
  FStarC_Tactics_Types.goal ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g ->
    let uu___ =
      let uu___1 = FStarC_Tactics_Types.goal_env g in
      let uu___2 = FStarC_Tactics_Types.goal_type g in
      FStarC_TypeChecker_Normalize.unfold_whnf uu___1 uu___2 in
    FStarC_Syntax_Util.un_squash uu___
let (is_irrelevant : FStarC_Tactics_Types.goal -> Prims.bool) =
  fun g -> let uu___ = get_phi g in FStarC_Compiler_Option.isSome uu___
let (goal_typedness_deps :
  FStarC_Tactics_Types.goal -> FStarC_Syntax_Syntax.ctx_uvar Prims.list) =
  fun g ->
    FStarC_Syntax_Util.ctx_uvar_typedness_deps
      g.FStarC_Tactics_Types.goal_ctx_uvar
let (set_uvar_expected_typ :
  FStarC_Syntax_Syntax.ctx_uvar -> FStarC_Syntax_Syntax.typ -> unit) =
  fun u ->
    fun t ->
      let dec =
        FStarC_Syntax_Unionfind.find_decoration
          u.FStarC_Syntax_Syntax.ctx_uvar_head in
      FStarC_Syntax_Unionfind.change_decoration
        u.FStarC_Syntax_Syntax.ctx_uvar_head
        {
          FStarC_Syntax_Syntax.uvar_decoration_typ = t;
          FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on);
          FStarC_Syntax_Syntax.uvar_decoration_should_check =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_should_check);
          FStarC_Syntax_Syntax.uvar_decoration_should_unrefine =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_should_unrefine)
        }
let (mark_uvar_with_should_check_tag :
  FStarC_Syntax_Syntax.ctx_uvar ->
    FStarC_Syntax_Syntax.should_check_uvar -> unit)
  =
  fun u ->
    fun sc ->
      let dec =
        FStarC_Syntax_Unionfind.find_decoration
          u.FStarC_Syntax_Syntax.ctx_uvar_head in
      FStarC_Syntax_Unionfind.change_decoration
        u.FStarC_Syntax_Syntax.ctx_uvar_head
        {
          FStarC_Syntax_Syntax.uvar_decoration_typ =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_typ);
          FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on);
          FStarC_Syntax_Syntax.uvar_decoration_should_check = sc;
          FStarC_Syntax_Syntax.uvar_decoration_should_unrefine =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_should_unrefine)
        }
let (mark_uvar_as_already_checked : FStarC_Syntax_Syntax.ctx_uvar -> unit) =
  fun u ->
    mark_uvar_with_should_check_tag u FStarC_Syntax_Syntax.Already_checked
let (mark_goal_implicit_already_checked : FStarC_Tactics_Types.goal -> unit)
  =
  fun g -> mark_uvar_as_already_checked g.FStarC_Tactics_Types.goal_ctx_uvar
let (goal_with_type :
  FStarC_Tactics_Types.goal ->
    FStarC_Syntax_Syntax.typ -> FStarC_Tactics_Types.goal)
  =
  fun g ->
    fun t ->
      let u = g.FStarC_Tactics_Types.goal_ctx_uvar in
      set_uvar_expected_typ u t; g
let divide : 'a 'b . FStarC_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun n ->
           fun l ->
             fun r ->
               Obj.magic
                 (FStarC_Class_Monad.op_let_Bang monad_tac () ()
                    (Obj.magic get)
                    (fun uu___ ->
                       (fun p ->
                          let p = Obj.magic p in
                          let uu___ =
                            try
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match () with
                                    | () ->
                                        let uu___2 =
                                          let uu___3 =
                                            FStarC_BigInt.to_int_fs n in
                                          FStarC_Compiler_List.splitAt uu___3
                                            p.FStarC_Tactics_Types.goals in
                                        Obj.magic
                                          (FStarC_Class_Monad.return
                                             monad_tac () (Obj.magic uu___2)))
                                   uu___1) ()
                            with | uu___1 -> fail "divide: not enough goals" in
                          Obj.magic
                            (FStarC_Class_Monad.op_let_Bang monad_tac () ()
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     let uu___1 = Obj.magic uu___1 in
                                     match uu___1 with
                                     | (lgs, rgs) ->
                                         let lp =
                                           {
                                             FStarC_Tactics_Types.main_context
                                               =
                                               (p.FStarC_Tactics_Types.main_context);
                                             FStarC_Tactics_Types.all_implicits
                                               =
                                               (p.FStarC_Tactics_Types.all_implicits);
                                             FStarC_Tactics_Types.goals = lgs;
                                             FStarC_Tactics_Types.smt_goals =
                                               [];
                                             FStarC_Tactics_Types.depth =
                                               (p.FStarC_Tactics_Types.depth);
                                             FStarC_Tactics_Types.__dump =
                                               (p.FStarC_Tactics_Types.__dump);
                                             FStarC_Tactics_Types.psc =
                                               (p.FStarC_Tactics_Types.psc);
                                             FStarC_Tactics_Types.entry_range
                                               =
                                               (p.FStarC_Tactics_Types.entry_range);
                                             FStarC_Tactics_Types.guard_policy
                                               =
                                               (p.FStarC_Tactics_Types.guard_policy);
                                             FStarC_Tactics_Types.freshness =
                                               (p.FStarC_Tactics_Types.freshness);
                                             FStarC_Tactics_Types.tac_verb_dbg
                                               =
                                               (p.FStarC_Tactics_Types.tac_verb_dbg);
                                             FStarC_Tactics_Types.local_state
                                               =
                                               (p.FStarC_Tactics_Types.local_state);
                                             FStarC_Tactics_Types.urgency =
                                               (p.FStarC_Tactics_Types.urgency);
                                             FStarC_Tactics_Types.dump_on_failure
                                               =
                                               (p.FStarC_Tactics_Types.dump_on_failure)
                                           } in
                                         let uu___2 = set lp in
                                         Obj.magic
                                           (FStarC_Class_Monad.op_let_Bang
                                              monad_tac () () uu___2
                                              (fun uu___3 ->
                                                 (fun uu___3 ->
                                                    let uu___3 =
                                                      Obj.magic uu___3 in
                                                    Obj.magic
                                                      (FStarC_Class_Monad.op_let_Bang
                                                         monad_tac () ()
                                                         (Obj.magic l)
                                                         (fun uu___4 ->
                                                            (fun a1 ->
                                                               let a1 =
                                                                 Obj.magic a1 in
                                                               Obj.magic
                                                                 (FStarC_Class_Monad.op_let_Bang
                                                                    monad_tac
                                                                    () ()
                                                                    (
                                                                    Obj.magic
                                                                    get)
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun lp'
                                                                    ->
                                                                    let lp' =
                                                                    Obj.magic
                                                                    lp' in
                                                                    let rp =
                                                                    {
                                                                    FStarC_Tactics_Types.main_context
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.main_context);
                                                                    FStarC_Tactics_Types.all_implicits
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.all_implicits);
                                                                    FStarC_Tactics_Types.goals
                                                                    = rgs;
                                                                    FStarC_Tactics_Types.smt_goals
                                                                    = [];
                                                                    FStarC_Tactics_Types.depth
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.depth);
                                                                    FStarC_Tactics_Types.__dump
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.__dump);
                                                                    FStarC_Tactics_Types.psc
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.psc);
                                                                    FStarC_Tactics_Types.entry_range
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.entry_range);
                                                                    FStarC_Tactics_Types.guard_policy
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.guard_policy);
                                                                    FStarC_Tactics_Types.freshness
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.freshness);
                                                                    FStarC_Tactics_Types.tac_verb_dbg
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.tac_verb_dbg);
                                                                    FStarC_Tactics_Types.local_state
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.local_state);
                                                                    FStarC_Tactics_Types.urgency
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.urgency);
                                                                    FStarC_Tactics_Types.dump_on_failure
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.dump_on_failure)
                                                                    } in
                                                                    let uu___4
                                                                    = set rp in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    monad_tac
                                                                    () ()
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    let uu___5
                                                                    =
                                                                    Obj.magic
                                                                    uu___5 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    r)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun b1
                                                                    ->
                                                                    let b1 =
                                                                    Obj.magic
                                                                    b1 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    get)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun rp'
                                                                    ->
                                                                    let rp' =
                                                                    Obj.magic
                                                                    rp' in
                                                                    let p' =
                                                                    {
                                                                    FStarC_Tactics_Types.main_context
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.main_context);
                                                                    FStarC_Tactics_Types.all_implicits
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.all_implicits);
                                                                    FStarC_Tactics_Types.goals
                                                                    =
                                                                    (FStarC_Compiler_List.op_At
                                                                    lp'.FStarC_Tactics_Types.goals
                                                                    rp'.FStarC_Tactics_Types.goals);
                                                                    FStarC_Tactics_Types.smt_goals
                                                                    =
                                                                    (FStarC_Compiler_List.op_At
                                                                    lp'.FStarC_Tactics_Types.smt_goals
                                                                    (FStarC_Compiler_List.op_At
                                                                    rp'.FStarC_Tactics_Types.smt_goals
                                                                    p.FStarC_Tactics_Types.smt_goals));
                                                                    FStarC_Tactics_Types.depth
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.depth);
                                                                    FStarC_Tactics_Types.__dump
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.__dump);
                                                                    FStarC_Tactics_Types.psc
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.psc);
                                                                    FStarC_Tactics_Types.entry_range
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.entry_range);
                                                                    FStarC_Tactics_Types.guard_policy
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.guard_policy);
                                                                    FStarC_Tactics_Types.freshness
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.freshness);
                                                                    FStarC_Tactics_Types.tac_verb_dbg
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.tac_verb_dbg);
                                                                    FStarC_Tactics_Types.local_state
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.local_state);
                                                                    FStarC_Tactics_Types.urgency
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.urgency);
                                                                    FStarC_Tactics_Types.dump_on_failure
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.dump_on_failure)
                                                                    } in
                                                                    let uu___6
                                                                    = set p' in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    monad_tac
                                                                    () ()
                                                                    uu___6
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    uu___7 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    monad_tac
                                                                    () ()
                                                                    remove_solved_goals
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    uu___8 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    (a1, b1))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                              uu___4)))
                                                   uu___3))) uu___1))) uu___)))
          uu___2 uu___1 uu___
let focus : 'a . 'a tac -> 'a tac =
  fun uu___ ->
    (fun f ->
       let uu___ =
         let uu___1 = FStarC_Class_Monad.return monad_tac () (Obj.repr ()) in
         divide FStarC_BigInt.one f uu___1 in
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang monad_tac () () (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  match uu___1 with
                  | (a1, uu___2) ->
                      Obj.magic
                        (FStarC_Class_Monad.return monad_tac ()
                           (Obj.magic a1))) uu___1))) uu___