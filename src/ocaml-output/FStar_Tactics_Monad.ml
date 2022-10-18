open Prims
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
         with
         | FStar_Errors.Err (uu___3, msg, uu___4) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Common.TacticFailure msg), ps)
         | FStar_Errors.Error (uu___3, msg, uu___4, uu___5) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Common.TacticFailure msg), ps)
         | e -> FStar_Tactics_Result.Failed (e, ps))
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
let op_let_Bang : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1 -> fun t2 -> bind t1 t2
let (idtac : unit tac) = ret ()
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun ps -> mk_tac (fun uu___ -> FStar_Tactics_Result.Success ((), ps))
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun ps -> FStar_Tactics_Result.Success (ps, ps))
let traise : 'a . Prims.exn -> 'a tac =
  fun e -> mk_tac (fun ps -> FStar_Tactics_Result.Failed (e, ps))
let (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps -> fun f -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
let fail : 'a . Prims.string -> 'a tac =
  fun msg ->
    mk_tac
      (fun ps ->
         (let uu___1 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu___1
          then
            FStar_Tactics_Printing.do_dump_proofstate ps
              (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Common.TacticFailure msg), ps))
let catch : 'a . 'a tac -> (Prims.exn, 'a) FStar_Pervasives.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu___ = run t ps in
         match uu___ with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Pervasives.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
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
                     (ps.FStar_Tactics_Types.urgency)
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
         | FStar_Errors.Err (uu___1, msg, uu___2) ->
             (log ps
                (fun uu___4 ->
                   FStar_Compiler_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu___1, msg, uu___2, uu___3) ->
             (log ps
                (fun uu___5 ->
                   FStar_Compiler_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f ->
    fun l ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu___ = f x in
          bind uu___
            (fun y ->
               let uu___1 = mapM f xs in
               bind uu___1 (fun ys -> ret (y :: ys)))
let (nwarn : Prims.int FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref Prims.int_zero
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g ->
    let uu___ = FStar_Options.defensive () in
    if uu___
    then
      let b = true in
      let env = FStar_Tactics_Types.goal_env g in
      let b1 =
        b &&
          (let uu___1 = FStar_Tactics_Types.goal_witness g in
           FStar_TypeChecker_Env.closed env uu___1) in
      let b2 =
        b1 &&
          (let uu___1 = FStar_Tactics_Types.goal_type g in
           FStar_TypeChecker_Env.closed env uu___1) in
      let rec aux b3 e =
        let uu___1 = FStar_TypeChecker_Env.pop_bv e in
        match uu___1 with
        | FStar_Pervasives_Native.None -> b3
        | FStar_Pervasives_Native.Some (bv, e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
            aux b4 e1 in
      let uu___1 =
        (let uu___2 = aux b2 env in Prims.op_Negation uu___2) &&
          (let uu___2 = FStar_Compiler_Effect.op_Bang nwarn in
           uu___2 < (Prims.of_int (5))) in
      (if uu___1
       then
         ((let uu___3 =
             let uu___4 = FStar_Tactics_Types.goal_type g in
             uu___4.FStar_Syntax_Syntax.pos in
           let uu___4 =
             let uu___5 =
               let uu___6 = FStar_Tactics_Printing.goal_to_string_verbose g in
               FStar_Compiler_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu___6 in
             (FStar_Errors.Warning_IllFormedGoal, uu___5) in
           FStar_Errors.log_issue uu___3 uu___4);
          (let uu___3 =
             let uu___4 = FStar_Compiler_Effect.op_Bang nwarn in
             uu___4 + Prims.int_one in
           FStar_Compiler_Effect.op_Colon_Equals nwarn uu___3))
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
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
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
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
           })
let (cur_goals : FStar_Tactics_Types.goal Prims.list tac) =
  bind get (fun ps -> ret ps.FStar_Tactics_Types.goals)
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
                  let uu___4 = FStar_Syntax_Print.term_to_string t in
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
           FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
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
              FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
            } in
          set uu___1))
let (getopts : FStar_Options.optionstate tac) =
  let uu___ = trytac cur_goal in
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
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
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
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
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
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
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
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
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
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
           })
let (new_uvar :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStar_Syntax_Syntax.ctx_uvar Prims.list ->
            FStar_Compiler_Range.range ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason ->
    fun env ->
      fun typ ->
        fun sc_opt ->
          fun apply_uvar_deps ->
            fun rng ->
              let should_check =
                match sc_opt with
                | FStar_Pervasives_Native.Some sc -> sc
                | uu___ ->
                    ((let uu___2 =
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "2635") in
                      if uu___2
                      then
                        let uu___3 = FStar_Syntax_Print.term_to_string typ in
                        FStar_Compiler_Util.print1
                          "Tactic introduced a strict uvar for %s\n" uu___3
                      else ());
                     FStar_Syntax_Syntax.Strict) in
              let uu___ =
                FStar_TypeChecker_Env.new_tac_implicit_var reason rng env typ
                  should_check FStar_Pervasives_Native.None apply_uvar_deps in
              match uu___ with
              | (u, ctx_uvar, g_u) ->
                  let uu___1 =
                    add_implicits g_u.FStar_TypeChecker_Common.implicits in
                  bind uu___1
                    (fun uu___2 ->
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = FStar_Compiler_List.hd ctx_uvar in
                           FStar_Pervasives_Native.fst uu___5 in
                         (u, uu___4) in
                       ret uu___3)
let (mk_irrelevant_goal :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Compiler_Range.range ->
          FStar_Options.optionstate ->
            Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun rng ->
          fun opts ->
            fun label ->
              let typ =
                let uu___ = env.FStar_TypeChecker_Env.universe_of env phi in
                FStar_Syntax_Util.mk_squash uu___ phi in
              let uu___ =
                new_uvar reason env typ
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Strict)
                  [] rng in
              bind uu___
                (fun uu___1 ->
                   match uu___1 with
                   | (uu___2, ctx_uvar) ->
                       let goal =
                         FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                           label in
                       ret goal)
let (add_irrelevant_goal' :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Compiler_Range.range ->
          FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun rng ->
          fun opts ->
            fun label ->
              let uu___ = mk_irrelevant_goal reason env phi rng opts label in
              bind uu___ (fun goal -> add_goals [goal])
let (add_irrelevant_goal :
  FStar_Tactics_Types.goal ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> unit tac)
  =
  fun base_goal ->
    fun reason ->
      fun env ->
        fun phi ->
          add_irrelevant_goal' reason env phi
            (base_goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
            base_goal.FStar_Tactics_Types.opts
            base_goal.FStar_Tactics_Types.label
let (goal_of_guard :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Compiler_Range.range -> FStar_Tactics_Types.goal tac)
  =
  fun reason ->
    fun e ->
      fun f ->
        fun rng ->
          bind getopts
            (fun opts ->
               let uu___ = mk_irrelevant_goal reason e f rng opts "" in
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
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      mk_tac
        (fun ps ->
           let uu___ = run t ps in
           match uu___ with
           | FStar_Tactics_Result.Success (a1, q) ->
               FStar_Tactics_Result.Success (a1, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Common.TacticFailure msg, q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Common.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e, q) ->
               FStar_Tactics_Result.Failed (e, q))
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f -> fun cont -> bind get (fun ps -> log ps f; cont ())
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
           FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
         } in
       set ps')