open Prims
let (dbg_Core : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "Core"
let (dbg_CoreEq : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "CoreEq"
let (dbg_RegisterGoal : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "RegisterGoal"
let (dbg_TacFail : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "TacFail"
let (goal_ctr : Prims.int FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref Prims.int_zero
let (get_goal_ctr : unit -> Prims.int) =
  fun uu___ -> FStar_Compiler_Effect.op_Bang goal_ctr
let (incr_goal_ctr : unit -> Prims.int) =
  fun uu___ ->
    let v = FStar_Compiler_Effect.op_Bang goal_ctr in
    FStar_Compiler_Effect.op_Colon_Equals goal_ctr (v + Prims.int_one); v
let (is_goal_safe_as_well_typed : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g ->
    let uv = g.FStar_Tactics_Types.goal_ctx_uvar in
    let all_deps_resolved =
      let uu___ = FStar_Syntax_Util.ctx_uvar_typedness_deps uv in
      FStar_Compiler_List.for_all
        (fun uv1 ->
           let uu___1 =
             FStar_Syntax_Unionfind.find
               uv1.FStar_Syntax_Syntax.ctx_uvar_head in
           match uu___1 with
           | FStar_Pervasives_Native.Some t ->
               let uu___2 = FStar_Syntax_Free.uvars t in
               FStar_Class_Setlike.is_empty ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___2)
           | uu___2 -> false) uu___ in
    all_deps_resolved
let (register_goal : FStar_Tactics_Types.goal -> unit) =
  fun g ->
    let uu___ =
      let uu___1 = FStar_Options.compat_pre_core_should_register () in
      Prims.op_Negation uu___1 in
    if uu___
    then ()
    else
      (let env = FStar_Tactics_Types.goal_env g in
       let uu___2 =
         env.FStar_TypeChecker_Env.phase1 || (FStar_Options.lax ()) in
       if uu___2
       then ()
       else
         (let uv = g.FStar_Tactics_Types.goal_ctx_uvar in
          let i = FStar_TypeChecker_Core.incr_goal_ctr () in
          let uu___4 =
            let uu___5 =
              FStar_Syntax_Util.ctx_uvar_should_check
                g.FStar_Tactics_Types.goal_ctx_uvar in
            FStar_Syntax_Syntax.uu___is_Allow_untyped uu___5 in
          if uu___4
          then ()
          else
            (let env1 =
               {
                 FStar_TypeChecker_Env.solver =
                   (env.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (env.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (env.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uv.FStar_Syntax_Syntax.ctx_uvar_gamma);
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
                 FStar_TypeChecker_Env.lax_universes =
                   (env.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (env.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (env.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.flychecking =
                   (env.FStar_TypeChecker_Env.flychecking);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (env.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.intactics =
                   (env.FStar_TypeChecker_Env.intactics);
                 FStar_TypeChecker_Env.nocoerce =
                   (env.FStar_TypeChecker_Env.nocoerce);
                 FStar_TypeChecker_Env.tc_term =
                   (env.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                   (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                 FStar_TypeChecker_Env.universe_of =
                   (env.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                   (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                 FStar_TypeChecker_Env.teq_nosmt_force =
                   (env.FStar_TypeChecker_Env.teq_nosmt_force);
                 FStar_TypeChecker_Env.subtype_nosmt_force =
                   (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (env.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (env.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (env.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (env.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
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
                 FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (env.FStar_TypeChecker_Env.strict_args_tab);
                 FStar_TypeChecker_Env.erasable_types_tab =
                   (env.FStar_TypeChecker_Env.erasable_types_tab);
                 FStar_TypeChecker_Env.enable_defer_to_tac =
                   (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                 FStar_TypeChecker_Env.unif_allow_ref_guards =
                   (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                 FStar_TypeChecker_Env.erase_erasable_args =
                   (env.FStar_TypeChecker_Env.erase_erasable_args);
                 FStar_TypeChecker_Env.core_check =
                   (env.FStar_TypeChecker_Env.core_check);
                 FStar_TypeChecker_Env.missing_decl =
                   (env.FStar_TypeChecker_Env.missing_decl)
               } in
             (let uu___7 = FStar_Compiler_Effect.op_Bang dbg_CoreEq in
              if uu___7
              then
                let uu___8 =
                  FStar_Class_Show.show
                    (FStar_Class_Show.printableshow
                       FStar_Class_Printable.printable_int) i in
                FStar_Compiler_Util.print1 "(%s) Registering goal\n" uu___8
              else ());
             (let should_register = is_goal_safe_as_well_typed g in
              if Prims.op_Negation should_register
              then
                let uu___8 =
                  (FStar_Compiler_Effect.op_Bang dbg_Core) ||
                    (FStar_Compiler_Effect.op_Bang dbg_RegisterGoal) in
                (if uu___8
                 then
                   let uu___9 =
                     FStar_Class_Show.show
                       (FStar_Class_Show.printableshow
                          FStar_Class_Printable.printable_int) i in
                   FStar_Compiler_Util.print1
                     "(%s) Not registering goal since it has unresolved uvar deps\n"
                     uu___9
                 else ())
              else
                ((let uu___9 =
                    (FStar_Compiler_Effect.op_Bang dbg_Core) ||
                      (FStar_Compiler_Effect.op_Bang dbg_RegisterGoal) in
                  if uu___9
                  then
                    let uu___10 =
                      FStar_Class_Show.show
                        (FStar_Class_Show.printableshow
                           FStar_Class_Printable.printable_int) i in
                    let uu___11 =
                      FStar_Class_Show.show FStar_Syntax_Print.showable_ctxu
                        uv in
                    FStar_Compiler_Util.print2
                      "(%s) Registering goal for %s\n" uu___10 uu___11
                  else ());
                 (let goal_ty = FStar_Syntax_Util.ctx_uvar_typ uv in
                  let uu___9 =
                    FStar_TypeChecker_Core.compute_term_type_handle_guards
                      env1 goal_ty (fun uu___10 -> fun uu___11 -> true) in
                  match uu___9 with
                  | FStar_Pervasives.Inl uu___10 -> ()
                  | FStar_Pervasives.Inr err ->
                      let msg =
                        let uu___10 =
                          let uu___11 = FStar_Syntax_Util.ctx_uvar_typ uv in
                          FStar_Class_Show.show
                            FStar_Syntax_Print.showable_term uu___11 in
                        let uu___11 =
                          FStar_TypeChecker_Core.print_error_short err in
                        FStar_Compiler_Util.format2
                          "Failed to check initial tactic goal %s because %s"
                          uu___10 uu___11 in
                      FStar_Errors.log_issue
                        FStar_Class_HasRange.hasRange_range
                        uv.FStar_Syntax_Syntax.ctx_uvar_range
                        FStar_Errors_Codes.Warning_FailedToCheckInitialTacticGoal
                        ()
                        (Obj.magic FStar_Errors_Msg.is_error_message_string)
                        (Obj.magic msg)))))))
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee -> match projectee with | { tac_f;_} -> tac_f
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f -> { tac_f = f }
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t -> fun ps -> t.tac_f ps
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      let uu___ = FStar_Options.tactics_failhard () in
      if uu___
      then run t ps
      else
        (try (fun uu___2 -> match () with | () -> run t ps) ()
         with | uu___2 -> FStar_Tactics_Result.Failed (uu___2, ps))
let ret : 'a . 'a -> 'a tac =
  fun x -> mk_tac (fun ps -> FStar_Tactics_Result.Success (x, ps))
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1 ->
    fun t2 ->
      mk_tac
        (fun ps ->
           let uu___ = run t1 ps in
           match uu___ with
           | FStar_Tactics_Result.Success (a1, q) ->
               let uu___1 = t2 a1 in run uu___1 q
           | FStar_Tactics_Result.Failed (msg, q) ->
               FStar_Tactics_Result.Failed (msg, q))
let (monad_tac : unit tac FStar_Class_Monad.monad) =
  {
    FStar_Class_Monad.return =
      (fun uu___1 -> fun uu___ -> (fun uu___ -> Obj.magic ret) uu___1 uu___);
    FStar_Class_Monad.op_let_Bang =
      (fun uu___3 ->
         fun uu___2 ->
           fun uu___1 ->
             fun uu___ ->
               (fun uu___1 -> fun uu___ -> Obj.magic bind) uu___3 uu___2
                 uu___1 uu___)
  }
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun ps -> mk_tac (fun uu___ -> FStar_Tactics_Result.Success ((), ps))
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun ps -> FStar_Tactics_Result.Success (ps, ps))
let traise : 'a . Prims.exn -> 'a tac =
  fun e -> mk_tac (fun ps -> FStar_Tactics_Result.Failed (e, ps))
let (do_log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps -> fun f -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
let (log : (unit -> unit) -> unit tac) =
  fun f ->
    mk_tac (fun ps -> do_log ps f; FStar_Tactics_Result.Success ((), ps))
let fail_doc : 'a . FStar_Errors_Msg.error_message -> 'a tac =
  fun msg ->
    mk_tac
      (fun ps ->
         (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_TacFail in
          if uu___1
          then
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Compiler_List.hd msg in
                FStar_Errors_Msg.renderdoc uu___4 in
              Prims.strcat "TACTIC FAILING: " uu___3 in
            FStar_Tactics_Printing.do_dump_proofstate ps uu___2
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Common.TacticFailure
               (msg, FStar_Pervasives_Native.None)), ps))
let fail : 'a . Prims.string -> 'a tac =
  fun msg ->
    let uu___ = let uu___1 = FStar_Errors_Msg.text msg in [uu___1] in
    fail_doc uu___
let catch : 'a . 'a tac -> (Prims.exn, 'a) FStar_Pervasives.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let idtable =
           FStar_Compiler_Effect.op_Bang
             (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.identifier_info in
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu___ = run t ps in
         match uu___ with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Pervasives.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Compiler_Effect.op_Colon_Equals
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.identifier_info
                idtable;
              (let ps1 =
                 {
                   FStar_Tactics_Types.main_context =
                     (ps.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (ps.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (ps.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (ps.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (ps.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (ps.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (ps.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (ps.FStar_Tactics_Types.local_state);
                   FStar_Tactics_Types.urgency =
                     (ps.FStar_Tactics_Types.urgency);
                   FStar_Tactics_Types.dump_on_failure =
                     (ps.FStar_Tactics_Types.dump_on_failure)
                 } in
               FStar_Tactics_Result.Success ((FStar_Pervasives.Inl m), ps1))))
let recover : 'a . 'a tac -> (Prims.exn, 'a) FStar_Pervasives.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let uu___ = run t ps in
         match uu___ with
         | FStar_Tactics_Result.Success (a1, q) ->
             FStar_Tactics_Result.Success ((FStar_Pervasives.Inr a1), q)
         | FStar_Tactics_Result.Failed (m, q) ->
             FStar_Tactics_Result.Success ((FStar_Pervasives.Inl m), q))
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
         | FStar_Errors.Error (uu___1, msg, uu___2, uu___3) ->
             (do_log ps
                (fun uu___5 ->
                   let uu___6 = FStar_Errors_Msg.rendermsg msg in
                   FStar_Compiler_Util.print1 "trytac_exn error: (%s)" uu___6);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let rec iter_tac : 'a . ('a -> unit tac) -> 'a Prims.list -> unit tac =
  fun f ->
    fun l ->
      match l with
      | [] -> ret ()
      | hd::tl ->
          let uu___ = f hd in
          FStar_Class_Monad.op_let_Bang monad_tac () () uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in Obj.magic (iter_tac f tl))
                 uu___1)
exception Bad of Prims.string 
let (uu___is_Bad : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Bad uu___ -> true | uu___ -> false
let (__proj__Bad__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Bad uu___ -> uu___
let (nwarn : Prims.int FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref Prims.int_zero
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g ->
    let uu___ = FStar_Options.defensive () in
    if uu___
    then
      try
        (fun uu___1 ->
           match () with
           | () ->
               let env = FStar_Tactics_Types.goal_env g in
               ((let uu___3 =
                   let uu___4 =
                     let uu___5 = FStar_Tactics_Types.goal_witness g in
                     FStar_TypeChecker_Env.closed env uu___5 in
                   Prims.op_Negation uu___4 in
                 if uu___3
                 then FStar_Compiler_Effect.raise (Bad "witness")
                 else ());
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Tactics_Types.goal_type g in
                     FStar_TypeChecker_Env.closed env uu___6 in
                   Prims.op_Negation uu___5 in
                 if uu___4
                 then FStar_Compiler_Effect.raise (Bad "goal type")
                 else ());
                (let rec aux e =
                   let uu___4 = FStar_TypeChecker_Env.pop_bv e in
                   match uu___4 with
                   | FStar_Pervasives_Native.None -> ()
                   | FStar_Pervasives_Native.Some (bv, e1) ->
                       ((let uu___6 =
                           let uu___7 =
                             FStar_TypeChecker_Env.closed e1
                               bv.FStar_Syntax_Syntax.sort in
                           Prims.op_Negation uu___7 in
                         if uu___6
                         then
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStar_Class_Show.show
                                   FStar_Syntax_Print.showable_bv bv in
                               Prims.strcat "bv: " uu___9 in
                             Bad uu___8 in
                           FStar_Compiler_Effect.raise uu___7
                         else ());
                        aux e1) in
                 aux env))) ()
      with
      | Bad culprit ->
          let uu___2 =
            let uu___3 = FStar_Compiler_Effect.op_Bang nwarn in
            uu___3 < (Prims.of_int (5)) in
          (if uu___2
           then
             ((let uu___4 = FStar_Tactics_Types.goal_type g in
               let uu___5 =
                 let uu___6 = FStar_Tactics_Printing.goal_to_string_verbose g in
                 FStar_Compiler_Util.format2
                   "The following goal is ill-formed (%s). Keeping calm and carrying on...\n<%s>\n\n"
                   culprit uu___6 in
               FStar_Errors.log_issue
                 (FStar_Syntax_Syntax.has_range_syntax ()) uu___4
                 FStar_Errors_Codes.Warning_IllFormedGoal ()
                 (Obj.magic FStar_Errors_Msg.is_error_message_string)
                 (Obj.magic uu___5));
              (let uu___4 =
                 let uu___5 = FStar_Compiler_Effect.op_Bang nwarn in
                 uu___5 + Prims.int_one in
               FStar_Compiler_Effect.op_Colon_Equals nwarn uu___4))
           else ())
    else ()
let (check_valid_goals : FStar_Tactics_Types.goal Prims.list -> unit) =
  fun gs ->
    let uu___ = FStar_Options.defensive () in
    if uu___ then FStar_Compiler_List.iter check_valid_goal gs else ()
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals = gs;
             FStar_Tactics_Types.smt_goals =
               (ps.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
             FStar_Tactics_Types.dump_on_failure =
               (ps.FStar_Tactics_Types.dump_on_failure)
           })
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals = gs;
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
             FStar_Tactics_Types.dump_on_failure =
               (ps.FStar_Tactics_Types.dump_on_failure)
           })
let (cur_goals : FStar_Tactics_Types.goal Prims.list tac) =
  bind get (fun ps -> ret ps.FStar_Tactics_Types.goals)
let (cur_goal_maybe_solved : FStar_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___ ->
       match uu___ with | [] -> fail "No more goals" | hd::tl -> ret hd)
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___ ->
       match uu___ with
       | [] -> fail "No more goals"
       | hd::tl ->
           let uu___1 = FStar_Tactics_Types.check_goal_solved' hd in
           (match uu___1 with
            | FStar_Pervasives_Native.None -> ret hd
            | FStar_Pervasives_Native.Some t ->
                ((let uu___3 =
                    FStar_Tactics_Printing.goal_to_string_verbose hd in
                  let uu___4 =
                    FStar_Class_Show.show FStar_Syntax_Print.showable_term t in
                  FStar_Compiler_Util.print2
                    "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                    uu___3 uu___4);
                 ret hd)))
let (remove_solved_goals : unit tac) =
  bind cur_goals
    (fun gs ->
       let gs1 =
         FStar_Compiler_List.filter
           (fun g ->
              let uu___ = FStar_Tactics_Types.check_goal_solved g in
              Prims.op_Negation uu___) gs in
       set_goals gs1)
let (dismiss_all : unit tac) = set_goals []
let (dismiss : unit tac) =
  bind get
    (fun ps ->
       let uu___ =
         let uu___1 = FStar_Compiler_List.tl ps.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (ps.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (ps.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu___1;
           FStar_Tactics_Types.smt_goals = (ps.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (ps.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (ps.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness = (ps.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (ps.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (ps.FStar_Tactics_Types.local_state);
           FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
           FStar_Tactics_Types.dump_on_failure =
             (ps.FStar_Tactics_Types.dump_on_failure)
         } in
       set uu___)
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g ->
    bind get
      (fun ps ->
         check_valid_goal g;
         (let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Compiler_List.tl ps.FStar_Tactics_Types.goals in
              g :: uu___3 in
            {
              FStar_Tactics_Types.main_context =
                (ps.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (ps.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = uu___2;
              FStar_Tactics_Types.smt_goals =
                (ps.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (ps.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (ps.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (ps.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (ps.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (ps.FStar_Tactics_Types.local_state);
              FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
              FStar_Tactics_Types.dump_on_failure =
                (ps.FStar_Tactics_Types.dump_on_failure)
            } in
          set uu___1))
let (getopts : FStar_Options.optionstate tac) =
  let uu___ = trytac cur_goal_maybe_solved in
  bind uu___
    (fun uu___1 ->
       match uu___1 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu___2 = FStar_Options.peek () in ret uu___2)
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (FStar_Compiler_List.op_At gs ps.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (ps.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
             FStar_Tactics_Types.dump_on_failure =
               (ps.FStar_Tactics_Types.dump_on_failure)
           })
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (FStar_Compiler_List.op_At gs ps.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
             FStar_Tactics_Types.dump_on_failure =
               (ps.FStar_Tactics_Types.dump_on_failure)
           })
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (FStar_Compiler_List.op_At ps.FStar_Tactics_Types.goals gs);
             FStar_Tactics_Types.smt_goals =
               (ps.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
             FStar_Tactics_Types.dump_on_failure =
               (ps.FStar_Tactics_Types.dump_on_failure)
           })
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (FStar_Compiler_List.op_At ps.FStar_Tactics_Types.smt_goals gs);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
             FStar_Tactics_Types.dump_on_failure =
               (ps.FStar_Tactics_Types.dump_on_failure)
           })
let (add_implicits : FStar_TypeChecker_Env.implicits -> unit tac) =
  fun i ->
    bind get
      (fun ps ->
         set
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (FStar_Compiler_List.op_At i
                  ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (ps.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
             FStar_Tactics_Types.dump_on_failure =
               (ps.FStar_Tactics_Types.dump_on_failure)
           })
let (new_uvar :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStar_Syntax_Syntax.ctx_uvar Prims.list ->
            FStar_Compiler_Range_Type.range ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
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
                | uu___ -> FStar_Syntax_Syntax.Strict in
              let uu___ =
                FStar_TypeChecker_Env.new_tac_implicit_var reason rng env typ
                  should_check uvar_typedness_deps
                  FStar_Pervasives_Native.None false in
              match uu___ with
              | (u, ctx_uvar, g_u) ->
                  let uu___1 =
                    add_implicits g_u.FStar_TypeChecker_Common.implicits in
                  bind uu___1
                    (fun uu___2 ->
                       ret (u, (FStar_Pervasives_Native.fst ctx_uvar)))
let (mk_irrelevant_goal :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStar_Compiler_Range_Type.range ->
            FStar_Options.optionstate ->
              Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun sc_opt ->
          fun rng ->
            fun opts ->
              fun label ->
                let typ =
                  let uu___ = env.FStar_TypeChecker_Env.universe_of env phi in
                  FStar_Syntax_Util.mk_squash uu___ phi in
                let uu___ = new_uvar reason env typ sc_opt [] rng in
                bind uu___
                  (fun uu___1 ->
                     match uu___1 with
                     | (uu___2, ctx_uvar) ->
                         let goal =
                           FStar_Tactics_Types.mk_goal env ctx_uvar opts
                             false label in
                         ret goal)
let (add_irrelevant_goal' :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStar_Compiler_Range_Type.range ->
            FStar_Options.optionstate -> Prims.string -> unit tac)
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
  FStar_Tactics_Types.goal ->
    Prims.string ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar
            FStar_Pervasives_Native.option -> unit tac)
  =
  fun base_goal ->
    fun reason ->
      fun env ->
        fun phi ->
          fun sc_opt ->
            add_irrelevant_goal' reason env phi sc_opt
              (base_goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
              base_goal.FStar_Tactics_Types.opts
              base_goal.FStar_Tactics_Types.label
let (goal_of_guard :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          -> FStar_Compiler_Range_Type.range -> FStar_Tactics_Types.goal tac)
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
                          FStar_Tactics_Types.goal_main_env =
                            (goal.FStar_Tactics_Types.goal_main_env);
                          FStar_Tactics_Types.goal_ctx_uvar =
                            (goal.FStar_Tactics_Types.goal_ctx_uvar);
                          FStar_Tactics_Types.opts =
                            (goal.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true;
                          FStar_Tactics_Types.label =
                            (goal.FStar_Tactics_Types.label)
                        } in
                      ret goal1))
let wrap_err_doc : 'a . FStar_Errors_Msg.error_message -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      mk_tac
        (fun ps ->
           let uu___ = run t ps in
           match uu___ with
           | FStar_Tactics_Result.Success (a1, q) ->
               FStar_Tactics_Result.Success (a1, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Common.TacticFailure (msg, r), q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Common.TacticFailure
                     ((FStar_Compiler_List.op_At pref msg), r)), q)
           | FStar_Tactics_Result.Failed (e, q) ->
               FStar_Tactics_Result.Failed (e, q))
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      let uu___ =
        let uu___1 =
          FStar_Errors_Msg.text
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
             (FStar_Class_Monad.op_let_Bang monad_tac () () uu___
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in Obj.magic (cont ()))
                     uu___1))) uu___1 uu___
let (if_verbose_tac : (unit -> unit tac) -> unit tac) =
  fun f ->
    FStar_Class_Monad.op_let_Bang monad_tac () () (Obj.magic get)
      (fun uu___ ->
         (fun ps ->
            let ps = Obj.magic ps in
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then Obj.magic (f ())
            else Obj.magic (ret ())) uu___)
let (if_verbose : (unit -> unit) -> unit tac) =
  fun f -> if_verbose_tac (fun uu___ -> f (); ret ())
let (compress_implicits : unit tac) =
  bind get
    (fun ps ->
       let imps = ps.FStar_Tactics_Types.all_implicits in
       let g =
         {
           FStar_TypeChecker_Common.guard_f =
             (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred_to_tac =
             (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
           FStar_TypeChecker_Common.deferred =
             (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         } in
       let imps1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g in
       let ps' =
         let uu___ =
           FStar_Compiler_List.map FStar_Pervasives_Native.fst imps1 in
         {
           FStar_Tactics_Types.main_context =
             (ps.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits = uu___;
           FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals = (ps.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (ps.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (ps.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness = (ps.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (ps.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (ps.FStar_Tactics_Types.local_state);
           FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency);
           FStar_Tactics_Types.dump_on_failure =
             (ps.FStar_Tactics_Types.dump_on_failure)
         } in
       set ps')
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g ->
    let uu___ =
      let uu___1 = FStar_Tactics_Types.goal_env g in
      let uu___2 = FStar_Tactics_Types.goal_type g in
      FStar_TypeChecker_Normalize.unfold_whnf uu___1 uu___2 in
    FStar_Syntax_Util.un_squash uu___
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g -> let uu___ = get_phi g in FStar_Compiler_Option.isSome uu___
let (goal_typedness_deps :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.ctx_uvar Prims.list) =
  fun g ->
    FStar_Syntax_Util.ctx_uvar_typedness_deps
      g.FStar_Tactics_Types.goal_ctx_uvar
let (set_uvar_expected_typ :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.typ -> unit) =
  fun u ->
    fun t ->
      let dec =
        FStar_Syntax_Unionfind.find_decoration
          u.FStar_Syntax_Syntax.ctx_uvar_head in
      FStar_Syntax_Unionfind.change_decoration
        u.FStar_Syntax_Syntax.ctx_uvar_head
        {
          FStar_Syntax_Syntax.uvar_decoration_typ = t;
          FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on =
            (dec.FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on);
          FStar_Syntax_Syntax.uvar_decoration_should_check =
            (dec.FStar_Syntax_Syntax.uvar_decoration_should_check);
          FStar_Syntax_Syntax.uvar_decoration_should_unrefine =
            (dec.FStar_Syntax_Syntax.uvar_decoration_should_unrefine)
        }
let (mark_uvar_with_should_check_tag :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.should_check_uvar -> unit)
  =
  fun u ->
    fun sc ->
      let dec =
        FStar_Syntax_Unionfind.find_decoration
          u.FStar_Syntax_Syntax.ctx_uvar_head in
      FStar_Syntax_Unionfind.change_decoration
        u.FStar_Syntax_Syntax.ctx_uvar_head
        {
          FStar_Syntax_Syntax.uvar_decoration_typ =
            (dec.FStar_Syntax_Syntax.uvar_decoration_typ);
          FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on =
            (dec.FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on);
          FStar_Syntax_Syntax.uvar_decoration_should_check = sc;
          FStar_Syntax_Syntax.uvar_decoration_should_unrefine =
            (dec.FStar_Syntax_Syntax.uvar_decoration_should_unrefine)
        }
let (mark_uvar_as_already_checked : FStar_Syntax_Syntax.ctx_uvar -> unit) =
  fun u ->
    mark_uvar_with_should_check_tag u FStar_Syntax_Syntax.Already_checked
let (mark_goal_implicit_already_checked : FStar_Tactics_Types.goal -> unit) =
  fun g -> mark_uvar_as_already_checked g.FStar_Tactics_Types.goal_ctx_uvar
let (goal_with_type :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.typ -> FStar_Tactics_Types.goal)
  =
  fun g ->
    fun t ->
      let u = g.FStar_Tactics_Types.goal_ctx_uvar in
      set_uvar_expected_typ u t; g
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun n ->
           fun l ->
             fun r ->
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang monad_tac () ()
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
                                            FStar_BigInt.to_int_fs n in
                                          FStar_Compiler_List.splitAt uu___3
                                            p.FStar_Tactics_Types.goals in
                                        Obj.magic
                                          (FStar_Class_Monad.return monad_tac
                                             () (Obj.magic uu___2))) uu___1)
                                ()
                            with | uu___1 -> fail "divide: not enough goals" in
                          Obj.magic
                            (FStar_Class_Monad.op_let_Bang monad_tac () ()
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     let uu___1 = Obj.magic uu___1 in
                                     match uu___1 with
                                     | (lgs, rgs) ->
                                         let lp =
                                           {
                                             FStar_Tactics_Types.main_context
                                               =
                                               (p.FStar_Tactics_Types.main_context);
                                             FStar_Tactics_Types.all_implicits
                                               =
                                               (p.FStar_Tactics_Types.all_implicits);
                                             FStar_Tactics_Types.goals = lgs;
                                             FStar_Tactics_Types.smt_goals =
                                               [];
                                             FStar_Tactics_Types.depth =
                                               (p.FStar_Tactics_Types.depth);
                                             FStar_Tactics_Types.__dump =
                                               (p.FStar_Tactics_Types.__dump);
                                             FStar_Tactics_Types.psc =
                                               (p.FStar_Tactics_Types.psc);
                                             FStar_Tactics_Types.entry_range
                                               =
                                               (p.FStar_Tactics_Types.entry_range);
                                             FStar_Tactics_Types.guard_policy
                                               =
                                               (p.FStar_Tactics_Types.guard_policy);
                                             FStar_Tactics_Types.freshness =
                                               (p.FStar_Tactics_Types.freshness);
                                             FStar_Tactics_Types.tac_verb_dbg
                                               =
                                               (p.FStar_Tactics_Types.tac_verb_dbg);
                                             FStar_Tactics_Types.local_state
                                               =
                                               (p.FStar_Tactics_Types.local_state);
                                             FStar_Tactics_Types.urgency =
                                               (p.FStar_Tactics_Types.urgency);
                                             FStar_Tactics_Types.dump_on_failure
                                               =
                                               (p.FStar_Tactics_Types.dump_on_failure)
                                           } in
                                         let uu___2 = set lp in
                                         Obj.magic
                                           (FStar_Class_Monad.op_let_Bang
                                              monad_tac () () uu___2
                                              (fun uu___3 ->
                                                 (fun uu___3 ->
                                                    let uu___3 =
                                                      Obj.magic uu___3 in
                                                    Obj.magic
                                                      (FStar_Class_Monad.op_let_Bang
                                                         monad_tac () ()
                                                         (Obj.magic l)
                                                         (fun uu___4 ->
                                                            (fun a1 ->
                                                               let a1 =
                                                                 Obj.magic a1 in
                                                               Obj.magic
                                                                 (FStar_Class_Monad.op_let_Bang
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
                                                                    FStar_Tactics_Types.main_context
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.main_context);
                                                                    FStar_Tactics_Types.all_implicits
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.all_implicits);
                                                                    FStar_Tactics_Types.goals
                                                                    = rgs;
                                                                    FStar_Tactics_Types.smt_goals
                                                                    = [];
                                                                    FStar_Tactics_Types.depth
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.depth);
                                                                    FStar_Tactics_Types.__dump
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.__dump);
                                                                    FStar_Tactics_Types.psc
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.psc);
                                                                    FStar_Tactics_Types.entry_range
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.entry_range);
                                                                    FStar_Tactics_Types.guard_policy
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.guard_policy);
                                                                    FStar_Tactics_Types.freshness
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.freshness);
                                                                    FStar_Tactics_Types.tac_verb_dbg
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.tac_verb_dbg);
                                                                    FStar_Tactics_Types.local_state
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.local_state);
                                                                    FStar_Tactics_Types.urgency
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.urgency);
                                                                    FStar_Tactics_Types.dump_on_failure
                                                                    =
                                                                    (lp'.FStar_Tactics_Types.dump_on_failure)
                                                                    } in
                                                                    let uu___4
                                                                    = set rp in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
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
                                                                    (FStar_Class_Monad.op_let_Bang
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
                                                                    (FStar_Class_Monad.op_let_Bang
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
                                                                    FStar_Tactics_Types.main_context
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.main_context);
                                                                    FStar_Tactics_Types.all_implicits
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.all_implicits);
                                                                    FStar_Tactics_Types.goals
                                                                    =
                                                                    (FStar_Compiler_List.op_At
                                                                    lp'.FStar_Tactics_Types.goals
                                                                    rp'.FStar_Tactics_Types.goals);
                                                                    FStar_Tactics_Types.smt_goals
                                                                    =
                                                                    (FStar_Compiler_List.op_At
                                                                    lp'.FStar_Tactics_Types.smt_goals
                                                                    (FStar_Compiler_List.op_At
                                                                    rp'.FStar_Tactics_Types.smt_goals
                                                                    p.FStar_Tactics_Types.smt_goals));
                                                                    FStar_Tactics_Types.depth
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.depth);
                                                                    FStar_Tactics_Types.__dump
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.__dump);
                                                                    FStar_Tactics_Types.psc
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.psc);
                                                                    FStar_Tactics_Types.entry_range
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.entry_range);
                                                                    FStar_Tactics_Types.guard_policy
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.guard_policy);
                                                                    FStar_Tactics_Types.freshness
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.freshness);
                                                                    FStar_Tactics_Types.tac_verb_dbg
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.tac_verb_dbg);
                                                                    FStar_Tactics_Types.local_state
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.local_state);
                                                                    FStar_Tactics_Types.urgency
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.urgency);
                                                                    FStar_Tactics_Types.dump_on_failure
                                                                    =
                                                                    (rp'.FStar_Tactics_Types.dump_on_failure)
                                                                    } in
                                                                    let uu___6
                                                                    = set p' in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
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
                                                                    (FStar_Class_Monad.op_let_Bang
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
                                                                    (FStar_Class_Monad.return
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
         let uu___1 = FStar_Class_Monad.return monad_tac () (Obj.repr ()) in
         divide FStar_BigInt.one f uu___1 in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang monad_tac () () (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  match uu___1 with
                  | (a1, uu___2) ->
                      Obj.magic
                        (FStar_Class_Monad.return monad_tac () (Obj.magic a1)))
                 uu___1))) uu___