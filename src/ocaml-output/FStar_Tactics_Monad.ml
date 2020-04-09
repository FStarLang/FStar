open Prims
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee  -> match projectee with | { tac_f;_} -> tac_f 
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f  -> { tac_f = f } 
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t  -> fun ps  -> t.tac_f ps 
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t  ->
    fun ps  ->
      let uu____114 = FStar_Options.tactics_failhard ()  in
      if uu____114
      then run t ps
      else
        (try (fun uu___20_124  -> match () with | () -> run t ps) ()
         with
         | FStar_Errors.Err (uu____133,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), ps)
         | FStar_Errors.Error (uu____137,msg,uu____139) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), ps)
         | e -> FStar_Tactics_Result.Failed (e, ps))
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun ps  -> FStar_Tactics_Result.Success (x, ps)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun ps  ->
           let uu____200 = run t1 ps  in
           match uu____200 with
           | FStar_Tactics_Result.Success (a1,q) ->
               let uu____207 = t2 a1  in run uu____207 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (idtac : unit tac) = ret () 
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun ps  -> mk_tac (fun uu____228  -> FStar_Tactics_Result.Success ((), ps)) 
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun ps  -> FStar_Tactics_Result.Success (ps, ps)) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____270 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____270
          then
            FStar_Tactics_Printing.do_dump_proofstate ps
              (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____323 = f x  in
          bind uu____323
            (fun y  ->
               let uu____331 = mapM f xs  in
               bind uu____331 (fun ys  -> ret (y :: ys)))
  
let (nwarn : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____358 = FStar_Options.defensive ()  in
    if uu____358
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____368 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____368)
         in
      let b2 =
        b1 &&
          (let uu____372 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____372)
         in
      let rec aux b3 e =
        let uu____387 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____387 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____407 =
        (let uu____411 = aux b2 env  in Prims.op_Negation uu____411) &&
          (let uu____414 = FStar_ST.op_Bang nwarn  in
           uu____414 < (Prims.of_int (5)))
         in
      (if uu____407
       then
         ((let uu____440 =
             let uu____441 = FStar_Tactics_Types.goal_type g  in
             uu____441.FStar_Syntax_Syntax.pos  in
           let uu____444 =
             let uu____450 =
               let uu____452 =
                 FStar_Tactics_Printing.goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____452
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____450)  in
           FStar_Errors.log_issue uu____440 uu____444);
          (let uu____456 =
             let uu____458 = FStar_ST.op_Bang nwarn  in
             uu____458 + Prims.int_one  in
           FStar_ST.op_Colon_Equals nwarn uu____456))
       else ())
    else ()
  
let (check_valid_goals : FStar_Tactics_Types.goal Prims.list -> unit) =
  fun gs  ->
    let uu____517 = FStar_Options.defensive ()  in
    if uu____517 then FStar_List.iter check_valid_goal gs else ()
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___96_540 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___96_540.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___96_540.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___96_540.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___96_540.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___96_540.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc = (uu___96_540.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___96_540.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___96_540.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___96_540.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___96_540.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___96_540.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___100_559 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_559.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___100_559.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___100_559.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___100_559.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_559.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_559.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_559.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_559.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_559.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___100_559.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___100_559.FStar_Tactics_Types.local_state)
            }))
  
let (cur_goals : FStar_Tactics_Types.goal Prims.list tac) =
  bind get (fun ps  -> ret ps.FStar_Tactics_Types.goals) 
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___0_579  ->
       match uu___0_579 with
       | [] -> fail "No more goals"
       | hd::tl ->
           let uu____589 = FStar_Tactics_Types.check_goal_solved' hd  in
           (match uu____589 with
            | FStar_Pervasives_Native.None  -> ret hd
            | FStar_Pervasives_Native.Some t ->
                ((let uu____596 =
                    FStar_Tactics_Printing.goal_to_string_verbose hd  in
                  let uu____598 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2
                    "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                    uu____596 uu____598);
                 ret hd)))
  
let (remove_solved_goals : unit tac) =
  bind cur_goals
    (fun gs  ->
       let gs1 =
         FStar_List.filter
           (fun g  ->
              let uu____619 = FStar_Tactics_Types.check_goal_solved g  in
              Prims.op_Negation uu____619) gs
          in
       set_goals gs1)
  
let (dismiss_all : unit tac) = set_goals [] 
let (dismiss : unit tac) =
  bind get
    (fun ps  ->
       let uu____634 =
         let uu___116_635 = ps  in
         let uu____636 = FStar_List.tl ps.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___116_635.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___116_635.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____636;
           FStar_Tactics_Types.smt_goals =
             (uu___116_635.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___116_635.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___116_635.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___116_635.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___116_635.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___116_635.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___116_635.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___116_635.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___116_635.FStar_Tactics_Types.local_state)
         }  in
       set uu____634)
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  ->
    bind get
      (fun ps  ->
         check_valid_goal g;
         (let uu____654 =
            let uu___121_655 = ps  in
            let uu____656 =
              let uu____659 = FStar_List.tl ps.FStar_Tactics_Types.goals  in
              g :: uu____659  in
            {
              FStar_Tactics_Types.main_context =
                (uu___121_655.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___121_655.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = uu____656;
              FStar_Tactics_Types.smt_goals =
                (uu___121_655.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___121_655.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___121_655.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___121_655.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___121_655.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___121_655.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___121_655.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___121_655.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___121_655.FStar_Tactics_Types.local_state)
            }  in
          set uu____654))
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         check_valid_goals gs;
         set
           (let uu___126_682 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___126_682.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___126_682.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___126_682.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___126_682.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___126_682.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___126_682.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___126_682.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___126_682.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___126_682.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___126_682.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___126_682.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         check_valid_goals gs;
         set
           (let uu___131_703 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___131_703.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___131_703.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___131_703.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___131_703.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___131_703.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___131_703.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___131_703.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___131_703.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___131_703.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___131_703.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___131_703.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         check_valid_goals gs;
         set
           (let uu___136_724 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___136_724.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___136_724.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append ps.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___136_724.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___136_724.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___136_724.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___136_724.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___136_724.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___136_724.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___136_724.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___136_724.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___136_724.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         check_valid_goals gs;
         set
           (let uu___141_745 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___141_745.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___141_745.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___141_745.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append ps.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___141_745.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___141_745.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___141_745.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___141_745.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___141_745.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___141_745.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___141_745.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___141_745.FStar_Tactics_Types.local_state)
            }))
  
let (add_implicits : FStar_TypeChecker_Env.implicits -> unit tac) =
  fun i  ->
    bind get
      (fun ps  ->
         set
           (let uu___145_760 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___145_760.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i ps.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___145_760.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___145_760.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___145_760.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___145_760.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___145_760.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___145_760.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___145_760.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___145_760.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___145_760.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___145_760.FStar_Tactics_Types.local_state)
            }))
  
let (new_uvar :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____791 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____791 with
        | (u,ctx_uvar,g_u) ->
            let uu____829 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits  in
            bind uu____829
              (fun uu____838  ->
                 let uu____839 =
                   let uu____844 =
                     let uu____845 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____845  in
                   (u, uu____844)  in
                 ret uu____839)
  
let (mk_irrelevant_goal :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label  ->
            let typ =
              let uu____895 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____895 phi  in
            let uu____896 = new_uvar reason env typ  in
            bind uu____896
              (fun uu____911  ->
                 match uu____911 with
                 | (uu____918,ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label
                        in
                     ret goal)
  
let (add_irrelevant_goal' :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label  ->
            let uu____956 = mk_irrelevant_goal reason env phi opts label  in
            bind uu____956 (fun goal  -> add_goals [goal])
  
let (add_irrelevant_goal :
  FStar_Tactics_Types.goal ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> unit tac)
  =
  fun base_goal  ->
    fun reason  ->
      fun env  ->
        fun phi  ->
          add_irrelevant_goal' reason env phi
            base_goal.FStar_Tactics_Types.opts
            base_goal.FStar_Tactics_Types.label
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1019 = run t ps  in
           match uu____1019 with
           | FStar_Tactics_Result.Success (a1,q) ->
               FStar_Tactics_Result.Success (a1, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Types.TacticFailure msg,q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Types.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e,q) ->
               FStar_Tactics_Result.Failed (e, q))
  
let (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___204_1102 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___204_1102.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred =
             (uu___204_1102.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___204_1102.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___208_1105 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___208_1105.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___208_1105.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___208_1105.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___208_1105.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___208_1105.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___208_1105.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___208_1105.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___208_1105.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___208_1105.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___208_1105.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___208_1105.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  