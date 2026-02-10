open Prims
type 'a tac = FStarC_Tactics_Types.proofstate FStarC_Effect.ref -> 'a
let dbg_Core : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Core"
let dbg_CoreEq : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "CoreEq"
let dbg_RegisterGoal : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "RegisterGoal"
let dbg_TacFail : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "TacFail"
let goal_ctr : Prims.int FStarC_Effect.ref=
  FStarC_Effect.mk_ref Prims.int_zero
let get_goal_ctr (uu___ : unit) : Prims.int= FStarC_Effect.op_Bang goal_ctr
let incr_goal_ctr (uu___ : unit) : Prims.int=
  let v = FStarC_Effect.op_Bang goal_ctr in
  FStarC_Effect.op_Colon_Equals goal_ctr (v + Prims.int_one); v
let is_goal_safe_as_well_typed (g : FStarC_Tactics_Types.goal) : Prims.bool=
  let uv = g.FStarC_Tactics_Types.goal_ctx_uvar in
  let all_deps_resolved =
    let uu___ = FStarC_Syntax_Util.ctx_uvar_typedness_deps uv in
    FStarC_List.for_all
      (fun uv1 ->
         let uu___1 =
           FStarC_Syntax_Unionfind.find
             uv1.FStarC_Syntax_Syntax.ctx_uvar_head in
         match uu___1 with
         | FStar_Pervasives_Native.Some t ->
             let uu___2 = FStarC_Syntax_Free.uvars t in
             FStarC_Class_Setlike.is_empty ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___2)
         | uu___2 -> false) uu___ in
  all_deps_resolved
let register_goal (g : FStarC_Tactics_Types.goal) : unit=
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
               FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
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
           (let uu___7 = FStarC_Effect.op_Bang dbg_CoreEq in
            if uu___7
            then
              let uu___8 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
              FStarC_Format.print1 "(%s) Registering goal\n" uu___8
            else ());
           (let should_register = is_goal_safe_as_well_typed g in
            if Prims.op_Negation should_register
            then
              let uu___8 =
                (FStarC_Effect.op_Bang dbg_Core) ||
                  (FStarC_Effect.op_Bang dbg_RegisterGoal) in
              (if uu___8
               then
                 let uu___9 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                 FStarC_Format.print1
                   "(%s) Not registering goal since it has unresolved uvar deps\n"
                   uu___9
               else ())
            else
              ((let uu___9 =
                  (FStarC_Effect.op_Bang dbg_Core) ||
                    (FStarC_Effect.op_Bang dbg_RegisterGoal) in
                if uu___9
                then
                  let uu___10 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                  let uu___11 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu
                      uv in
                  FStarC_Format.print2 "(%s) Registering goal for %s\n"
                    uu___10 uu___11
                else ());
               (let goal_ty = FStarC_Syntax_Util.ctx_uvar_typ uv in
                let uu___9 =
                  FStarC_TypeChecker_Core.compute_term_type env1 goal_ty in
                match uu___9 with
                | FStar_Pervasives.Inl
                    (uu___10, uu___11, FStar_Pervasives_Native.None) -> ()
                | FStar_Pervasives.Inl
                    (uu___10, uu___11, FStar_Pervasives_Native.Some
                     (g1, tok))
                    -> FStarC_TypeChecker_Core.commit_guard tok
                | FStar_Pervasives.Inr err ->
                    let msg =
                      let uu___10 =
                        let uu___11 = FStarC_Syntax_Util.ctx_uvar_typ uv in
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term uu___11 in
                      let uu___11 =
                        FStarC_TypeChecker_Core.print_error_short err in
                      FStarC_Format.fmt2
                        "Failed to check initial tactic goal %s because %s"
                        uu___10 uu___11 in
                    FStarC_Errors.log_issue
                      FStarC_Class_HasRange.hasRange_range
                      uv.FStarC_Syntax_Syntax.ctx_uvar_range
                      FStarC_Errors_Codes.Warning_FailedToCheckInitialTacticGoal
                      ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                      (Obj.magic msg)))))))
let mk_tac
  (f : FStarC_Tactics_Types.proofstate -> 'a FStarC_Tactics_Result.__result)
  : 'a tac=
  fun ps ->
    let uu___ = let uu___1 = FStarC_Effect.op_Bang ps in f uu___1 in
    match uu___ with
    | FStarC_Tactics_Result.Success (x, ps') ->
        (FStarC_Effect.op_Colon_Equals ps ps'; x)
let run (t : 'a tac) (ps : FStarC_Tactics_Types.proofstate) :
  'a FStarC_Tactics_Result.__result=
  let ps1 = FStarC_Effect.mk_ref ps in
  let x = t ps1 in
  let uu___ = let uu___1 = FStarC_Effect.op_Bang ps1 in (x, uu___1) in
  FStarC_Tactics_Result.Success uu___
let run_safe (t : 'a tac) (ps : FStarC_Tactics_Types.proofstate) :
  'a FStarC_Tactics_Result.__result= run t ps
let ret (x : 'a) : 'a tac= fun uu___ -> x
let bind (t1 : 'a tac) (t2 : 'a -> 'b tac) : 'b tac=
  fun ps -> let x = t1 ps in let uu___ = t2 x in uu___ ps
let monad_tac : unit tac FStarC_Class_Monad.monad=
  {
    FStarC_Class_Monad.return =
      (fun uu___1 uu___ -> (fun uu___ -> Obj.magic ret) uu___1 uu___);
    FStarC_Class_Monad.bind =
      (fun uu___3 uu___2 uu___1 uu___ ->
         (fun uu___1 uu___ -> Obj.magic bind) uu___3 uu___2 uu___1 uu___)
  }
let set (ps : FStarC_Tactics_Types.proofstate) : unit tac=
  fun ps_ref -> FStarC_Effect.op_Colon_Equals ps_ref ps
let get : FStarC_Tactics_Types.proofstate tac=
  fun ps -> FStarC_Effect.op_Bang ps
let traise (e : Prims.exn) : 'a tac= fun uu___ -> FStarC_Effect.raise e
let do_log (ps : FStarC_Tactics_Types.proofstate) (f : unit -> unit) : 
  unit= if ps.FStarC_Tactics_Types.tac_verb_dbg then f () else ()
let log (f : unit -> unit) : unit tac=
  fun ps -> let uu___ = FStarC_Effect.op_Bang ps in do_log uu___ f
let fail_doc (msg : FStarC_Errors_Msg.error_message) : 'a tac=
  fun ps ->
    (let uu___1 = FStarC_Effect.op_Bang dbg_TacFail in
     if uu___1
     then
       let uu___2 = FStarC_Effect.op_Bang ps in
       let uu___3 =
         let uu___4 =
           let uu___5 = FStarC_List.hd msg in
           FStarC_Errors_Msg.renderdoc uu___5 in
         Prims.strcat "TACTIC FAILING: " uu___4 in
       FStarC_Tactics_Printing.do_dump_proofstate uu___2 uu___3
     else ());
    FStarC_Effect.raise
      (FStarC_Tactics_Common.TacticFailure
         (msg, FStar_Pervasives_Native.None))
let fail (msg : Prims.string) : 'a tac=
  let uu___ = let uu___1 = FStarC_Errors_Msg.text msg in [uu___1] in
  fail_doc uu___
let catch (t : 'a tac) : (Prims.exn, 'a) FStar_Pervasives.either tac=
  mk_tac
    (fun ps ->
       let idtable =
         FStarC_Effect.op_Bang
           (ps.FStarC_Tactics_Types.main_context).FStarC_TypeChecker_Env.identifier_info in
       let tx = FStarC_Syntax_Unionfind.new_transaction () in
       try
         (fun uu___ ->
            match () with
            | () ->
                let uu___1 = run t ps in
                (match uu___1 with
                 | FStarC_Tactics_Result.Success (a1, q) ->
                     (FStarC_Syntax_Unionfind.commit tx;
                      FStarC_Tactics_Result.Success
                        ((FStar_Pervasives.Inr a1), q)))) ()
       with
       | uu___ ->
           (FStarC_Syntax_Unionfind.rollback tx;
            FStarC_Effect.op_Colon_Equals
              (ps.FStarC_Tactics_Types.main_context).FStarC_TypeChecker_Env.identifier_info
              idtable;
            FStarC_Tactics_Result.Success ((FStar_Pervasives.Inl uu___), ps)))
let trytac (t : 'a tac) : 'a FStar_Pervasives_Native.option tac=
  let uu___ = catch t in
  bind uu___
    (fun r ->
       match r with
       | FStar_Pervasives.Inr v -> ret (FStar_Pervasives_Native.Some v)
       | FStar_Pervasives.Inl uu___1 -> ret FStar_Pervasives_Native.None)
let trytac_exn (t : 'a tac) : 'a FStar_Pervasives_Native.option tac=
  mk_tac
    (fun ps ->
       try
         (fun uu___ ->
            match () with | () -> let uu___1 = trytac t in run uu___1 ps) ()
       with
       | FStarC_Errors.Error (uu___1, msg, uu___2, uu___3) ->
           (do_log ps
              (fun uu___5 ->
                 let uu___6 = FStarC_Errors_Msg.rendermsg msg in
                 FStarC_Format.print1 "trytac_exn error: (%s)" uu___6);
            FStarC_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let rec iter_tac : 'a . ('a -> unit tac) -> 'a Prims.list -> unit tac =
  fun f l ->
    match l with
    | [] -> ret ()
    | hd::tl ->
        let uu___ = f hd in
        FStarC_Class_Monad.op_let_Bang monad_tac () () uu___
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___1 = Obj.magic uu___1 in Obj.magic (iter_tac f tl))
               uu___1)
let rec fold_right :
  'a 'b . ('a -> 'b -> 'b tac) -> 'a Prims.list -> 'b -> 'b tac =
  fun uu___2 uu___1 uu___ ->
    (fun f l x ->
       match l with
       | [] ->
           Obj.magic (FStarC_Class_Monad.return monad_tac () (Obj.magic x))
       | hd::tl ->
           let uu___ = fold_right f tl x in
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang monad_tac () ()
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun r -> let r = Obj.magic r in Obj.magic (f hd r))
                     uu___1))) uu___2 uu___1 uu___
exception Bad of Prims.string 
let uu___is_Bad (projectee : Prims.exn) : Prims.bool=
  match projectee with | Bad uu___ -> true | uu___ -> false
let __proj__Bad__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | Bad uu___ -> uu___
let nwarn : Prims.int FStarC_Effect.ref= FStarC_Effect.mk_ref Prims.int_zero
let check_valid_goal (g : FStarC_Tactics_Types.goal) : unit=
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
               if uu___3 then FStarC_Effect.raise (Bad "witness") else ());
              (let uu___4 =
                 let uu___5 =
                   let uu___6 = FStarC_Tactics_Types.goal_type g in
                   FStarC_TypeChecker_Env.closed env uu___6 in
                 Prims.op_Negation uu___5 in
               if uu___4 then FStarC_Effect.raise (Bad "goal type") else ());
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
                         FStarC_Effect.raise uu___7
                       else ());
                      aux e1) in
               aux env))) ()
    with
    | Bad culprit ->
        let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang nwarn in
          uu___3 < (Prims.of_int (5)) in
        (if uu___2
         then
           ((let uu___4 = FStarC_Tactics_Types.goal_type g in
             let uu___5 =
               let uu___6 = FStarC_Tactics_Printing.goal_to_string_verbose g in
               FStarC_Format.fmt2
                 "The following goal is ill-formed (%s). Keeping calm and carrying on...\n<%s>\n\n"
                 culprit uu___6 in
             FStarC_Errors.log_issue
               (FStarC_Syntax_Syntax.has_range_syntax ()) uu___4
               FStarC_Errors_Codes.Warning_IllFormedGoal ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic uu___5));
            (let uu___4 =
               let uu___5 = FStarC_Effect.op_Bang nwarn in
               uu___5 + Prims.int_one in
             FStarC_Effect.op_Colon_Equals nwarn uu___4))
         else ())
  else ()
let check_valid_goals (gs : FStarC_Tactics_Types.goal Prims.list) : unit=
  let uu___ = FStarC_Options.defensive () in
  if uu___ then FStarC_List.iter check_valid_goal gs else ()
let set_goals (gs : FStarC_Tactics_Types.goal Prims.list) : unit tac=
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
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let set_smt_goals (gs : FStarC_Tactics_Types.goal Prims.list) : unit tac=
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
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let cur_goals : FStarC_Tactics_Types.goal Prims.list tac=
  bind get (fun ps -> ret ps.FStarC_Tactics_Types.goals)
let cur_goal_maybe_solved : FStarC_Tactics_Types.goal tac=
  bind cur_goals
    (fun uu___ ->
       match uu___ with | [] -> fail "No more goals" | hd::tl -> ret hd)
let cur_goal : FStarC_Tactics_Types.goal tac=
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
                  FStarC_Format.print2
                    "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                    uu___3 uu___4);
                 ret hd)))
let remove_solved_goals : unit tac=
  bind cur_goals
    (fun gs ->
       let gs1 =
         FStarC_List.filter
           (fun g ->
              let uu___ = FStarC_Tactics_Types.check_goal_solved g in
              Prims.op_Negation uu___) gs in
       set_goals gs1)
let dismiss_all : unit tac= set_goals []
let dismiss : unit tac=
  bind get
    (fun ps ->
       let uu___ =
         let uu___1 = FStarC_List.tl ps.FStarC_Tactics_Types.goals in
         {
           FStarC_Tactics_Types.main_context =
             (ps.FStarC_Tactics_Types.main_context);
           FStarC_Tactics_Types.all_implicits =
             (ps.FStarC_Tactics_Types.all_implicits);
           FStarC_Tactics_Types.goals = uu___1;
           FStarC_Tactics_Types.smt_goals =
             (ps.FStarC_Tactics_Types.smt_goals);
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let replace_cur (g : FStarC_Tactics_Types.goal) : unit tac=
  bind get
    (fun ps ->
       check_valid_goal g;
       (let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_List.tl ps.FStarC_Tactics_Types.goals in g ::
              uu___3 in
          {
            FStarC_Tactics_Types.main_context =
              (ps.FStarC_Tactics_Types.main_context);
            FStarC_Tactics_Types.all_implicits =
              (ps.FStarC_Tactics_Types.all_implicits);
            FStarC_Tactics_Types.goals = uu___2;
            FStarC_Tactics_Types.smt_goals =
              (ps.FStarC_Tactics_Types.smt_goals);
            FStarC_Tactics_Types.splice_quals =
              (ps.FStarC_Tactics_Types.splice_quals);
            FStarC_Tactics_Types.splice_attrs =
              (ps.FStarC_Tactics_Types.splice_attrs);
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
        set uu___1))
let getopts : FStarC_Options.optionstate tac=
  let uu___ = trytac cur_goal_maybe_solved in
  bind uu___
    (fun uu___1 ->
       match uu___1 with
       | FStar_Pervasives_Native.Some g -> ret g.FStarC_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu___2 = FStarC_Options.peek () in ret uu___2)
let add_goals (gs : FStarC_Tactics_Types.goal Prims.list) : unit tac=
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
             (FStarC_List.op_At gs ps.FStarC_Tactics_Types.goals);
           FStarC_Tactics_Types.smt_goals =
             (ps.FStarC_Tactics_Types.smt_goals);
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let add_smt_goals (gs : FStarC_Tactics_Types.goal Prims.list) : unit tac=
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
             (FStarC_List.op_At gs ps.FStarC_Tactics_Types.smt_goals);
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let push_goals (gs : FStarC_Tactics_Types.goal Prims.list) : unit tac=
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
             (FStarC_List.op_At ps.FStarC_Tactics_Types.goals gs);
           FStarC_Tactics_Types.smt_goals =
             (ps.FStarC_Tactics_Types.smt_goals);
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let push_smt_goals (gs : FStarC_Tactics_Types.goal Prims.list) : unit tac=
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
             (FStarC_List.op_At ps.FStarC_Tactics_Types.smt_goals gs);
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let add_implicits (i : FStarC_TypeChecker_Env.implicits) : unit tac=
  bind get
    (fun ps ->
       set
         {
           FStarC_Tactics_Types.main_context =
             (ps.FStarC_Tactics_Types.main_context);
           FStarC_Tactics_Types.all_implicits =
             (FStarC_List.op_At i ps.FStarC_Tactics_Types.all_implicits);
           FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
           FStarC_Tactics_Types.smt_goals =
             (ps.FStarC_Tactics_Types.smt_goals);
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let new_uvar (reason : Prims.string) (env : FStarC_TypeChecker_Env.env)
  (typ : FStarC_Syntax_Syntax.typ)
  (sc_opt :
    FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option)
  (uvar_typedness_deps : FStarC_Syntax_Syntax.ctx_uvar Prims.list)
  (rng : FStarC_Range_Type.t) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.ctx_uvar) tac=
  let should_check =
    match sc_opt with
    | FStar_Pervasives_Native.Some sc -> sc
    | uu___ -> FStarC_Syntax_Syntax.Strict in
  let uu___ =
    FStarC_TypeChecker_Env.new_tac_implicit_var reason rng env typ
      should_check uvar_typedness_deps FStar_Pervasives_Native.None false in
  match uu___ with
  | (u, ctx_uvar, g_u) ->
      let uu___1 =
        let uu___2 =
          FStarC_Class_Listlike.to_list (FStarC_CList.listlike_clist ())
            g_u.FStarC_TypeChecker_Common.implicits in
        add_implicits uu___2 in
      bind uu___1
        (fun uu___2 -> ret (u, (FStar_Pervasives_Native.fst ctx_uvar)))
let mk_irrelevant_goal (reason : Prims.string)
  (env : FStarC_TypeChecker_Env.env) (phi : FStarC_Syntax_Syntax.typ)
  (sc_opt :
    FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option)
  (rng : FStarC_Range_Type.t) (opts : FStarC_Options.optionstate)
  (label : Prims.string) : FStarC_Tactics_Types.goal tac=
  let typ =
    let uu___ = env.FStarC_TypeChecker_Env.universe_of env phi in
    FStarC_Syntax_Util.mk_squash uu___ phi in
  let uu___ = new_uvar reason env typ sc_opt [] rng in
  bind uu___
    (fun uu___1 ->
       match uu___1 with
       | (uu___2, ctx_uvar) ->
           let goal =
             FStarC_Tactics_Types.mk_goal env ctx_uvar opts false label in
           ret goal)
let add_irrelevant_goal' (reason : Prims.string)
  (env : FStarC_TypeChecker_Env.env) (phi : FStarC_Syntax_Syntax.term)
  (sc_opt :
    FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option)
  (rng : FStarC_Range_Type.t) (opts : FStarC_Options.optionstate)
  (label : Prims.string) : unit tac=
  let uu___ = mk_irrelevant_goal reason env phi sc_opt rng opts label in
  bind uu___ (fun goal -> add_goals [goal])
let add_irrelevant_goal (base_goal : FStarC_Tactics_Types.goal)
  (reason : Prims.string) (env : FStarC_TypeChecker_Env.env)
  (phi : FStarC_Syntax_Syntax.term)
  (sc_opt :
    FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option)
  : unit tac=
  add_irrelevant_goal' reason env phi sc_opt
    (base_goal.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_range
    base_goal.FStarC_Tactics_Types.opts base_goal.FStarC_Tactics_Types.label
let goal_of_guard (reason : Prims.string) (e : FStarC_TypeChecker_Env.env)
  (f : FStarC_Syntax_Syntax.term)
  (sc_opt :
    FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option)
  (rng : FStarC_Range_Type.t) : FStarC_Tactics_Types.goal tac=
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
                FStarC_Tactics_Types.opts = (goal.FStarC_Tactics_Types.opts);
                FStarC_Tactics_Types.is_guard = true;
                FStarC_Tactics_Types.label =
                  (goal.FStarC_Tactics_Types.label)
              } in
            ret goal1))
let wrap_err_doc (pref : FStarC_Errors_Msg.error_message) (t : 'a tac) :
  'a tac=
  mk_tac
    (fun ps ->
       try (fun uu___ -> match () with | () -> run t ps) ()
       with
       | FStarC_Tactics_Common.TacticFailure (msg, r) ->
           FStarC_Effect.raise
             (FStarC_Tactics_Common.TacticFailure
                ((FStarC_List.op_At pref msg), r))
       | e -> FStarC_Effect.raise e)
let wrap_err (pref : Prims.string) (t : 'a tac) : 'a tac=
  let uu___ =
    let uu___1 =
      FStarC_Errors_Msg.text
        (Prims.strcat "'" (Prims.strcat pref "' failed")) in
    [uu___1] in
  wrap_err_doc uu___ t
let mlog (uu___1 : unit -> unit) (uu___ : unit -> 'a tac) : 'a tac=
  (fun f cont ->
     let uu___ = log f in
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang monad_tac () () uu___
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___1 = Obj.magic uu___1 in Obj.magic (cont ())) uu___1)))
    uu___1 uu___
let if_verbose_tac (f : unit -> unit tac) : unit tac=
  FStarC_Class_Monad.op_let_Bang monad_tac () () (Obj.magic get)
    (fun uu___ ->
       (fun ps ->
          let ps = Obj.magic ps in
          if ps.FStarC_Tactics_Types.tac_verb_dbg
          then Obj.magic (f ())
          else Obj.magic (ret ())) uu___)
let if_verbose (f : unit -> unit) : unit tac=
  if_verbose_tac (fun uu___ -> f (); ret ())
let compress_implicits : unit tac=
  bind get
    (fun ps ->
       let imps = ps.FStarC_Tactics_Types.all_implicits in
       let g =
         let uu___ =
           FStarC_Class_Listlike.from_list (FStarC_CList.listlike_clist ())
             imps in
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
         let uu___ = FStarC_List.map FStar_Pervasives_Native.fst imps1 in
         {
           FStarC_Tactics_Types.main_context =
             (ps.FStarC_Tactics_Types.main_context);
           FStarC_Tactics_Types.all_implicits = uu___;
           FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
           FStarC_Tactics_Types.smt_goals =
             (ps.FStarC_Tactics_Types.smt_goals);
           FStarC_Tactics_Types.splice_quals =
             (ps.FStarC_Tactics_Types.splice_quals);
           FStarC_Tactics_Types.splice_attrs =
             (ps.FStarC_Tactics_Types.splice_attrs);
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
let get_phi (g : FStarC_Tactics_Types.goal) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Tactics_Types.goal_env g in
    let uu___2 = FStarC_Tactics_Types.goal_type g in
    FStarC_TypeChecker_Normalize.unfold_whnf uu___1 uu___2 in
  FStarC_Syntax_Util.un_squash uu___
let is_irrelevant (g : FStarC_Tactics_Types.goal) : Prims.bool=
  let uu___ = get_phi g in FStar_Pervasives_Native.uu___is_Some uu___
let goal_typedness_deps (g : FStarC_Tactics_Types.goal) :
  FStarC_Syntax_Syntax.ctx_uvar Prims.list=
  FStarC_Syntax_Util.ctx_uvar_typedness_deps
    g.FStarC_Tactics_Types.goal_ctx_uvar
let set_uvar_expected_typ (u : FStarC_Syntax_Syntax.ctx_uvar)
  (t : FStarC_Syntax_Syntax.typ) : unit=
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
let mark_uvar_with_should_check_tag (u : FStarC_Syntax_Syntax.ctx_uvar)
  (sc : FStarC_Syntax_Syntax.should_check_uvar) : unit=
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
let mark_uvar_as_already_checked (u : FStarC_Syntax_Syntax.ctx_uvar) : 
  unit=
  mark_uvar_with_should_check_tag u FStarC_Syntax_Syntax.Already_checked
let mark_goal_implicit_already_checked (g : FStarC_Tactics_Types.goal) :
  unit= mark_uvar_as_already_checked g.FStarC_Tactics_Types.goal_ctx_uvar
let goal_with_type (g : FStarC_Tactics_Types.goal)
  (t : FStarC_Syntax_Syntax.typ) : FStarC_Tactics_Types.goal=
  let u = g.FStarC_Tactics_Types.goal_ctx_uvar in
  set_uvar_expected_typ u t; g
let divide (uu___2 : Prims.int) (uu___1 : 'a tac) (uu___ : 'b tac) :
  ('a * 'b) tac=
  (fun n l r ->
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang monad_tac () () (Obj.magic get)
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
                                FStarC_List.splitAt n
                                  p.FStarC_Tactics_Types.goals in
                              Obj.magic
                                (FStarC_Class_Monad.return monad_tac ()
                                   (Obj.magic uu___2))) uu___1) ()
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
                                   FStarC_Tactics_Types.main_context =
                                     (p.FStarC_Tactics_Types.main_context);
                                   FStarC_Tactics_Types.all_implicits =
                                     (p.FStarC_Tactics_Types.all_implicits);
                                   FStarC_Tactics_Types.goals = lgs;
                                   FStarC_Tactics_Types.smt_goals = [];
                                   FStarC_Tactics_Types.splice_quals =
                                     (p.FStarC_Tactics_Types.splice_quals);
                                   FStarC_Tactics_Types.splice_attrs =
                                     (p.FStarC_Tactics_Types.splice_attrs);
                                   FStarC_Tactics_Types.depth =
                                     (p.FStarC_Tactics_Types.depth);
                                   FStarC_Tactics_Types.__dump =
                                     (p.FStarC_Tactics_Types.__dump);
                                   FStarC_Tactics_Types.psc =
                                     (p.FStarC_Tactics_Types.psc);
                                   FStarC_Tactics_Types.entry_range =
                                     (p.FStarC_Tactics_Types.entry_range);
                                   FStarC_Tactics_Types.guard_policy =
                                     (p.FStarC_Tactics_Types.guard_policy);
                                   FStarC_Tactics_Types.freshness =
                                     (p.FStarC_Tactics_Types.freshness);
                                   FStarC_Tactics_Types.tac_verb_dbg =
                                     (p.FStarC_Tactics_Types.tac_verb_dbg);
                                   FStarC_Tactics_Types.local_state =
                                     (p.FStarC_Tactics_Types.local_state);
                                   FStarC_Tactics_Types.urgency =
                                     (p.FStarC_Tactics_Types.urgency);
                                   FStarC_Tactics_Types.dump_on_failure =
                                     (p.FStarC_Tactics_Types.dump_on_failure)
                                 } in
                               let uu___2 = set lp in
                               Obj.magic
                                 (FStarC_Class_Monad.op_let_Bang monad_tac ()
                                    () uu___2
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          let uu___3 = Obj.magic uu___3 in
                                          Obj.magic
                                            (FStarC_Class_Monad.op_let_Bang
                                               monad_tac () () (Obj.magic l)
                                               (fun uu___4 ->
                                                  (fun a1 ->
                                                     let a1 = Obj.magic a1 in
                                                     Obj.magic
                                                       (FStarC_Class_Monad.op_let_Bang
                                                          monad_tac () ()
                                                          (Obj.magic get)
                                                          (fun uu___4 ->
                                                             (fun lp' ->
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
                                                                    FStarC_Tactics_Types.splice_quals
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.splice_quals);
                                                                    FStarC_Tactics_Types.splice_attrs
                                                                    =
                                                                    (lp'.FStarC_Tactics_Types.splice_attrs);
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
                                                                let uu___4 =
                                                                  set rp in
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
                                                                    (FStarC_List.op_At
                                                                    lp'.FStarC_Tactics_Types.goals
                                                                    rp'.FStarC_Tactics_Types.goals);
                                                                    FStarC_Tactics_Types.smt_goals
                                                                    =
                                                                    (FStarC_List.op_At
                                                                    lp'.FStarC_Tactics_Types.smt_goals
                                                                    (FStarC_List.op_At
                                                                    rp'.FStarC_Tactics_Types.smt_goals
                                                                    p.FStarC_Tactics_Types.smt_goals));
                                                                    FStarC_Tactics_Types.splice_quals
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.splice_quals);
                                                                    FStarC_Tactics_Types.splice_attrs
                                                                    =
                                                                    (rp'.FStarC_Tactics_Types.splice_attrs);
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
                                                    uu___4))) uu___3)))
                          uu___1))) uu___))) uu___2 uu___1 uu___
let focus (uu___ : 'a tac) : 'a tac=
  (fun f ->
     let uu___ =
       let uu___1 = FStarC_Class_Monad.return monad_tac () (Obj.repr ()) in
       divide Prims.int_one f uu___1 in
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang monad_tac () () (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___1 = Obj.magic uu___1 in
                match uu___1 with
                | (a1, uu___2) ->
                    Obj.magic
                      (FStarC_Class_Monad.return monad_tac () (Obj.magic a1)))
               uu___1))) uu___
