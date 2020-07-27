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
      let uu____111 = FStar_Options.tactics_failhard () in
      if uu____111
      then run t ps
      else
        (try (fun uu___20_118 -> match () with | () -> run t ps) ()
         with
         | FStar_Errors.Err (uu____127, msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), ps)
         | FStar_Errors.Error (uu____129, msg, uu____131) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), ps)
         | e -> FStar_Tactics_Result.Failed (e, ps))
let ret : 'a . 'a -> 'a tac =
  fun x -> mk_tac (fun ps -> FStar_Tactics_Result.Success (x, ps))
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1 ->
    fun t2 ->
      mk_tac
        (fun ps ->
           let uu____188 = run t1 ps in
           match uu____188 with
           | FStar_Tactics_Result.Success (a1, q) ->
               let uu____195 = t2 a1 in run uu____195 q
           | FStar_Tactics_Result.Failed (msg, q) ->
               FStar_Tactics_Result.Failed (msg, q))
let (idtac : unit tac) = ret ()
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun ps -> mk_tac (fun uu____214 -> FStar_Tactics_Result.Success ((), ps))
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun ps -> FStar_Tactics_Result.Success (ps, ps))
let traise : 'a . Prims.exn -> 'a tac =
  fun e -> mk_tac (fun ps -> FStar_Tactics_Result.Failed (e, ps))
let fail : 'a . Prims.string -> 'a tac =
  fun msg ->
    mk_tac
      (fun ps ->
         (let uu____251 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____251
          then
            FStar_Tactics_Printing.do_dump_proofstate ps
              (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f ->
    fun l ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____298 = f x in
          bind uu____298
            (fun y ->
               let uu____306 = mapM f xs in
               bind uu____306 (fun ys -> ret (y :: ys)))
let (nwarn : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g ->
    let uu____328 = FStar_Options.defensive () in
    if uu____328
    then
      let b = true in
      let env = FStar_Tactics_Types.goal_env g in
      let b1 =
        b &&
          (let uu____333 = FStar_Tactics_Types.goal_witness g in
           FStar_TypeChecker_Env.closed env uu____333) in
      let b2 =
        b1 &&
          (let uu____336 = FStar_Tactics_Types.goal_type g in
           FStar_TypeChecker_Env.closed env uu____336) in
      let rec aux b3 e =
        let uu____348 = FStar_TypeChecker_Env.pop_bv e in
        match uu____348 with
        | FStar_Pervasives_Native.None -> b3
        | FStar_Pervasives_Native.Some (bv, e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
            aux b4 e1 in
      let uu____366 =
        (let uu____369 = aux b2 env in Prims.op_Negation uu____369) &&
          (let uu____371 = FStar_ST.op_Bang nwarn in
           uu____371 < (Prims.of_int (5))) in
      (if uu____366
       then
         ((let uu____379 =
             let uu____380 = FStar_Tactics_Types.goal_type g in
             uu____380.FStar_Syntax_Syntax.pos in
           let uu____383 =
             let uu____388 =
               let uu____389 =
                 FStar_Tactics_Printing.goal_to_string_verbose g in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____389 in
             (FStar_Errors.Warning_IllFormedGoal, uu____388) in
           FStar_Errors.log_issue uu____379 uu____383);
          (let uu____390 =
             let uu____391 = FStar_ST.op_Bang nwarn in
             uu____391 + Prims.int_one in
           FStar_ST.op_Colon_Equals nwarn uu____390))
       else ())
    else ()
let (check_valid_goals : FStar_Tactics_Types.goal Prims.list -> unit) =
  fun gs ->
    let uu____415 = FStar_Options.defensive () in
    if uu____415 then FStar_List.iter check_valid_goal gs else ()
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___96_434 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___96_434.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___96_434.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___96_434.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___96_434.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___96_434.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc = (uu___96_434.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___96_434.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___96_434.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___96_434.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___96_434.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___96_434.FStar_Tactics_Types.local_state)
            }))
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___100_452 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_452.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___100_452.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___100_452.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___100_452.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_452.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_452.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_452.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_452.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_452.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___100_452.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___100_452.FStar_Tactics_Types.local_state)
            }))
let (cur_goals : FStar_Tactics_Types.goal Prims.list tac) =
  bind get (fun ps -> ret ps.FStar_Tactics_Types.goals)
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___0_470 ->
       match uu___0_470 with
       | [] -> fail "No more goals"
       | hd::tl ->
           let uu____479 = FStar_Tactics_Types.check_goal_solved' hd in
           (match uu____479 with
            | FStar_Pervasives_Native.None -> ret hd
            | FStar_Pervasives_Native.Some t ->
                ((let uu____486 =
                    FStar_Tactics_Printing.goal_to_string_verbose hd in
                  let uu____487 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                    uu____486 uu____487);
                 ret hd)))
let (remove_solved_goals : unit tac) =
  bind cur_goals
    (fun gs ->
       let gs1 =
         FStar_List.filter
           (fun g ->
              let uu____505 = FStar_Tactics_Types.check_goal_solved g in
              Prims.op_Negation uu____505) gs in
       set_goals gs1)
let (dismiss_all : unit tac) = set_goals []
let (dismiss : unit tac) =
  bind get
    (fun ps ->
       let uu____517 =
         let uu___116_518 = ps in
         let uu____519 = FStar_List.tl ps.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___116_518.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___116_518.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____519;
           FStar_Tactics_Types.smt_goals =
             (uu___116_518.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___116_518.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___116_518.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___116_518.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___116_518.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___116_518.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___116_518.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___116_518.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___116_518.FStar_Tactics_Types.local_state)
         } in
       set uu____517)
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g ->
    bind get
      (fun ps ->
         check_valid_goal g;
         (let uu____536 =
            let uu___121_537 = ps in
            let uu____538 =
              let uu____541 = FStar_List.tl ps.FStar_Tactics_Types.goals in g
                :: uu____541 in
            {
              FStar_Tactics_Types.main_context =
                (uu___121_537.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___121_537.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = uu____538;
              FStar_Tactics_Types.smt_goals =
                (uu___121_537.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___121_537.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___121_537.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___121_537.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___121_537.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___121_537.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___121_537.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___121_537.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___121_537.FStar_Tactics_Types.local_state)
            } in
          set uu____536))
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___126_563 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___126_563.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___126_563.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___126_563.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___126_563.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___126_563.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___126_563.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___126_563.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___126_563.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___126_563.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___126_563.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___126_563.FStar_Tactics_Types.local_state)
            }))
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___131_583 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___131_583.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___131_583.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___131_583.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___131_583.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___131_583.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___131_583.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___131_583.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___131_583.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___131_583.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___131_583.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___131_583.FStar_Tactics_Types.local_state)
            }))
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___136_603 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___136_603.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___136_603.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append ps.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___136_603.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___136_603.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___136_603.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___136_603.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___136_603.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___136_603.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___136_603.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___136_603.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___136_603.FStar_Tactics_Types.local_state)
            }))
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___141_623 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___141_623.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___141_623.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___141_623.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append ps.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___141_623.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___141_623.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___141_623.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___141_623.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___141_623.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___141_623.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___141_623.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___141_623.FStar_Tactics_Types.local_state)
            }))
let (add_implicits : FStar_TypeChecker_Env.implicits -> unit tac) =
  fun i ->
    bind get
      (fun ps ->
         set
           (let uu___145_637 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___145_637.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i ps.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___145_637.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___145_637.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___145_637.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___145_637.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___145_637.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___145_637.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___145_637.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___145_637.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___145_637.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___145_637.FStar_Tactics_Types.local_state)
            }))
let (new_uvar :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason ->
    fun env ->
      fun typ ->
        let uu____665 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
        match uu____665 with
        | (u, ctx_uvar, g_u) ->
            let uu____699 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits in
            bind uu____699
              (fun uu____708 ->
                 let uu____709 =
                   let uu____714 =
                     let uu____715 = FStar_List.hd ctx_uvar in
                     FStar_Pervasives_Native.fst uu____715 in
                   (u, uu____714) in
                 ret uu____709)
let (mk_irrelevant_goal :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun opts ->
          fun label ->
            let typ =
              let uu____760 = env.FStar_TypeChecker_Env.universe_of env phi in
              FStar_Syntax_Util.mk_squash uu____760 phi in
            let uu____761 = new_uvar reason env typ in
            bind uu____761
              (fun uu____776 ->
                 match uu____776 with
                 | (uu____783, ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label in
                     ret goal)
let (add_irrelevant_goal' :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun opts ->
          fun label ->
            let uu____815 = mk_irrelevant_goal reason env phi opts label in
            bind uu____815 (fun goal -> add_goals [goal])
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
            base_goal.FStar_Tactics_Types.opts
            base_goal.FStar_Tactics_Types.label
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      mk_tac
        (fun ps ->
           let uu____872 = run t ps in
           match uu____872 with
           | FStar_Tactics_Result.Success (a1, q) ->
               FStar_Tactics_Result.Success (a1, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Types.TacticFailure msg, q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Types.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e, q) ->
               FStar_Tactics_Result.Failed (e, q))
let (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps -> fun f -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f -> fun cont -> bind get (fun ps -> log ps f; cont ())
let (compress_implicits : unit tac) =
  bind get
    (fun ps ->
       let imps = ps.FStar_Tactics_Types.all_implicits in
       let g =
         let uu___204_948 = FStar_TypeChecker_Env.trivial_guard in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___204_948.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred_to_tac =
             (uu___204_948.FStar_TypeChecker_Common.deferred_to_tac);
           FStar_TypeChecker_Common.deferred =
             (uu___204_948.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___204_948.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         } in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g in
       let ps' =
         let uu___208_951 = ps in
         {
           FStar_Tactics_Types.main_context =
             (uu___208_951.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___208_951.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___208_951.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___208_951.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___208_951.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___208_951.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___208_951.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___208_951.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___208_951.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___208_951.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___208_951.FStar_Tactics_Types.local_state)
         } in
       set ps')