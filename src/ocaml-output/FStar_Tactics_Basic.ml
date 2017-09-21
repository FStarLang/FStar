open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let normalize:
  FStar_TypeChecker_Normalize.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
let bnorm:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> normalize [] e t
type goal =
  {
  context: env;
  witness: FStar_Syntax_Syntax.term;
  goal_ty: FStar_Syntax_Syntax.typ;
  opts: FStar_Options.optionstate;}
let __proj__Mkgoal__item__context: goal -> env =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__context
let __proj__Mkgoal__item__witness: goal -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__witness
let __proj__Mkgoal__item__goal_ty: goal -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__goal_ty
let __proj__Mkgoal__item__opts: goal -> FStar_Options.optionstate =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} -> __fname__opts
type proofstate =
  {
  main_context: env;
  main_goal: goal;
  all_implicits: implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;}
let __proj__Mkproofstate__item__main_context: proofstate -> env =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__main_context
let __proj__Mkproofstate__item__main_goal: proofstate -> goal =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__main_goal
let __proj__Mkproofstate__item__all_implicits: proofstate -> implicits =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__all_implicits
let __proj__Mkproofstate__item__goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__goals
let __proj__Mkproofstate__item__smt_goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__smt_goals
type 'a result =
  | Success of ('a,proofstate) FStar_Pervasives_Native.tuple2
  | Failed of (Prims.string,proofstate) FStar_Pervasives_Native.tuple2
let uu___is_Success: 'a . 'a result -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____211 -> false
let __proj__Success__item___0:
  'a . 'a result -> ('a,proofstate) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: 'a . 'a result -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____257 -> false
let __proj__Failed__item___0:
  'a . 'a result -> (Prims.string,proofstate) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____292 -> true | uu____293 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____301 -> uu____301
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let __proj__Mktac__item__tac_f: 'a . 'a tac -> proofstate -> 'a result =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
let mk_tac: 'a . (proofstate -> 'a result) -> 'a tac =
  fun f  -> { tac_f = f }
let run: 'Auu____365 . 'Auu____365 tac -> proofstate -> 'Auu____365 result =
  fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac = fun x  -> mk_tac (fun p  -> Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____432 = run t1 p in
           match uu____432 with
           | Success (a,q) -> let uu____439 = t2 a in run uu____439 q
           | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____451 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____451
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____452 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____453 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____452 uu____453
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____466 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____466
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____479 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____479
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____496 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____496
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____502) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____512) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____526 =
      let uu____531 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____531 in
    match uu____526 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____537 -> false
let dump_goal: 'Auu____548 . 'Auu____548 -> goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____558 = goal_to_string goal in tacprint uu____558
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____568 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____572 = FStar_List.hd ps.goals in dump_goal ps uu____572))
let ps_to_string:
  (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> Prims.string =
  fun uu____580  ->
    match uu____580 with
    | (msg,ps) ->
        let uu____587 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
        let uu____588 =
          let uu____589 = FStar_List.map goal_to_string ps.goals in
          FStar_String.concat "\n" uu____589 in
        let uu____592 =
          FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
        let uu____593 =
          let uu____594 = FStar_List.map goal_to_string ps.smt_goals in
          FStar_String.concat "\n" uu____594 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____587 uu____588 uu____592 uu____593
let goal_to_json: goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____602 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____602 FStar_Syntax_Print.binders_to_json in
    let uu____603 =
      let uu____610 =
        let uu____617 =
          let uu____622 =
            let uu____623 =
              let uu____630 =
                let uu____635 =
                  let uu____636 = FStar_Syntax_Print.term_to_string g.witness in
                  FStar_Util.JsonStr uu____636 in
                ("witness", uu____635) in
              let uu____637 =
                let uu____644 =
                  let uu____649 =
                    let uu____650 =
                      FStar_Syntax_Print.term_to_string g.goal_ty in
                    FStar_Util.JsonStr uu____650 in
                  ("type", uu____649) in
                [uu____644] in
              uu____630 :: uu____637 in
            FStar_Util.JsonAssoc uu____623 in
          ("goal", uu____622) in
        [uu____617] in
      ("hyps", g_binders) :: uu____610 in
    FStar_Util.JsonAssoc uu____603
let ps_to_json:
  (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____682  ->
    match uu____682 with
    | (msg,ps) ->
        let uu____689 =
          let uu____696 =
            let uu____703 =
              let uu____708 =
                let uu____709 = FStar_List.map goal_to_json ps.goals in
                FStar_Util.JsonList uu____709 in
              ("goals", uu____708) in
            let uu____712 =
              let uu____719 =
                let uu____724 =
                  let uu____725 = FStar_List.map goal_to_json ps.smt_goals in
                  FStar_Util.JsonList uu____725 in
                ("smt-goals", uu____724) in
              [uu____719] in
            uu____703 :: uu____712 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____696 in
        FStar_Util.JsonAssoc uu____689
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____754  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
let print_proof_state1: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_cur p msg; Success ((), p))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let tac_verb_dbg: Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec log: proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun ps  ->
    fun f  ->
      let uu____814 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____814 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____836 =
              let uu____839 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____839 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____836);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____879 . Prims.string -> 'Auu____879 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____890 =
            FStar_TypeChecker_Env.debug ps.main_context
              (FStar_Options.Other "TacFail") in
          if uu____890
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         Failed (msg, ps))
let fail1: 'Auu____898 . Prims.string -> Prims.string -> 'Auu____898 tac =
  fun msg  ->
    fun x  -> let uu____909 = FStar_Util.format1 msg x in fail uu____909
let fail2:
  'Auu____918 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____918 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____933 = FStar_Util.format2 msg x y in fail uu____933
let fail3:
  'Auu____944 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____944 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____963 = FStar_Util.format3 msg x y z in fail uu____963
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____991 = run t ps in
         match uu____991 with
         | Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              Success ((FStar_Pervasives_Native.Some a), q))
         | Failed (uu____1005,uu____1006) ->
             (FStar_Syntax_Unionfind.rollback tx;
              Success (FStar_Pervasives_Native.None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____1040  -> Success ((), p))
let trysolve: goal -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun goal  ->
    fun solution  ->
      FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____1057 = trysolve goal solution in
      if uu____1057
      then ()
      else
        (let uu____1059 =
           let uu____1060 =
             let uu____1061 =
               FStar_TypeChecker_Normalize.term_to_string goal.context
                 solution in
             let uu____1062 =
               FStar_TypeChecker_Normalize.term_to_string goal.context
                 goal.witness in
             let uu____1063 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____1061
               uu____1062 uu____1063 in
           TacFailure uu____1060 in
         FStar_Exn.raise uu____1059)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____1069 =
         let uu___88_1070 = p in
         let uu____1071 = FStar_List.tl p.goals in
         {
           main_context = (uu___88_1070.main_context);
           main_goal = (uu___88_1070.main_goal);
           all_implicits = (uu___88_1070.all_implicits);
           goals = uu____1071;
           smt_goals = (uu___88_1070.smt_goals)
         } in
       set uu____1069)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___89_1080 = p in
          {
            main_context = (uu___89_1080.main_context);
            main_goal = (uu___89_1080.main_goal);
            all_implicits = (uu___89_1080.all_implicits);
            goals = [];
            smt_goals = (uu___89_1080.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_1097 = p in
            {
              main_context = (uu___90_1097.main_context);
              main_goal = (uu___90_1097.main_goal);
              all_implicits = (uu___90_1097.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___90_1097.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_1114 = p in
            {
              main_context = (uu___91_1114.main_context);
              main_goal = (uu___91_1114.main_goal);
              all_implicits = (uu___91_1114.all_implicits);
              goals = (uu___91_1114.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1131 = p in
            {
              main_context = (uu___92_1131.main_context);
              main_goal = (uu___92_1131.main_goal);
              all_implicits = (uu___92_1131.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___92_1131.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___93_1148 = p in
            {
              main_context = (uu___93_1148.main_context);
              main_goal = (uu___93_1148.main_goal);
              all_implicits = (uu___93_1148.all_implicits);
              goals = (uu___93_1148.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1158  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___94_1171 = p in
            {
              main_context = (uu___94_1171.main_context);
              main_goal = (uu___94_1171.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___94_1171.goals);
              smt_goals = (uu___94_1171.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____1196 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1196 with
      | (u,uu____1212,g_u) ->
          let uu____1226 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1226 (fun uu____1230  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1235 = FStar_Syntax_Util.un_squash t in
    match uu____1235 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1245 =
          let uu____1246 = FStar_Syntax_Subst.compress t' in
          uu____1246.FStar_Syntax_Syntax.n in
        (match uu____1245 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1250 -> false)
    | uu____1251 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1260 = FStar_Syntax_Util.un_squash t in
    match uu____1260 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1270 =
          let uu____1271 = FStar_Syntax_Subst.compress t' in
          uu____1271.FStar_Syntax_Syntax.n in
        (match uu____1270 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1275 -> false)
    | uu____1276 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let mk_irrelevant_goal:
  env -> FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> goal tac =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let typ = FStar_Syntax_Util.mk_squash phi in
        let uu____1310 = new_uvar env typ in
        bind uu____1310
          (fun u  ->
             let goal = { context = env; witness = u; goal_ty = typ; opts } in
             ret goal)
let add_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let uu____1333 = mk_irrelevant_goal env phi opts in
        bind uu____1333 (fun goal  -> add_goals [goal])
let istrivial: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac] in
      let t1 = normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1356 = istrivial goal.context goal.goal_ty in
       if uu____1356
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1361 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1361))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1378 =
          let uu____1379 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1379.FStar_TypeChecker_Env.guard_f in
        match uu____1378 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1383 = istrivial e f in
            if uu____1383
            then ret ()
            else
              (let uu____1387 = mk_irrelevant_goal e f opts in
               bind uu____1387
                 (fun goal  ->
                    let goal1 =
                      let uu___95_1394 = goal in
                      {
                        context = (uu___95_1394.context);
                        witness = (uu___95_1394.witness);
                        goal_ty = (uu___95_1394.goal_ty);
                        opts = (uu___95_1394.opts);
                        is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1400 = is_irrelevant g in
       if uu____1400
       then bind dismiss (fun uu____1404  -> add_smt_goals [g])
       else
         (let uu____1406 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1406))
let divide:
  'a 'b .
    Prims.int ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____1452 =
               try
                 let uu____1486 = FStar_List.splitAt n1 p.goals in
                 ret uu____1486
               with | uu____1516 -> fail "divide: not enough goals" in
             bind uu____1452
               (fun uu____1543  ->
                  match uu____1543 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___96_1569 = p in
                        {
                          main_context = (uu___96_1569.main_context);
                          main_goal = (uu___96_1569.main_goal);
                          all_implicits = (uu___96_1569.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___97_1571 = p in
                        {
                          main_context = (uu___97_1571.main_context);
                          main_goal = (uu___97_1571.main_goal);
                          all_implicits = (uu___97_1571.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1572 = set lp in
                      bind uu____1572
                        (fun uu____1580  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1594 = set rp in
                                     bind uu____1594
                                       (fun uu____1602  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___98_1618 = p in
                                                      {
                                                        main_context =
                                                          (uu___98_1618.main_context);
                                                        main_goal =
                                                          (uu___98_1618.main_goal);
                                                        all_implicits =
                                                          (uu___98_1618.all_implicits);
                                                        goals =
                                                          (FStar_List.append
                                                             lp'.goals
                                                             rp'.goals);
                                                        smt_goals =
                                                          (FStar_List.append
                                                             lp'.smt_goals
                                                             (FStar_List.append
                                                                rp'.smt_goals
                                                                p.smt_goals))
                                                      } in
                                                    let uu____1619 = set p' in
                                                    bind uu____1619
                                                      (fun uu____1627  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1647 = divide (Prims.parse_int "1") f idtac in
    bind uu____1647
      (fun uu____1660  -> match uu____1660 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1695::uu____1696 ->
             let uu____1699 =
               let uu____1708 = map tau in
               divide (Prims.parse_int "1") tau uu____1708 in
             bind uu____1699
               (fun uu____1726  ->
                  match uu____1726 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1765 =
        bind t1
          (fun uu____1770  ->
             let uu____1771 = map t2 in
             bind uu____1771 (fun uu____1779  -> ret ())) in
      focus uu____1765
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1790 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1790 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1805 =
             let uu____1806 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1806 in
           if uu____1805
           then fail "Codomain is effectful"
           else
             (let env' = FStar_TypeChecker_Env.push_binders goal.context [b] in
              let typ' = comp_to_typ c in
              let uu____1812 = new_uvar env' typ' in
              bind uu____1812
                (fun u  ->
                   let uu____1819 =
                     let uu____1820 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1820 in
                   if uu____1819
                   then
                     let uu____1823 =
                       let uu____1826 =
                         let uu___101_1827 = goal in
                         let uu____1828 = bnorm env' u in
                         let uu____1829 = bnorm env' typ' in
                         {
                           context = env';
                           witness = uu____1828;
                           goal_ty = uu____1829;
                           opts = (uu___101_1827.opts);
                           is_guard = (uu___101_1827.is_guard)
                         } in
                       replace_cur uu____1826 in
                     bind uu____1823 (fun uu____1831  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1837 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1837)
let intro_rec:
  (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____1858 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1858 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1877 =
              let uu____1878 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1878 in
            if uu____1877
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None goal.goal_ty in
               let bs =
                 let uu____1894 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1894; b] in
               let env' = FStar_TypeChecker_Env.push_binders goal.context bs in
               let uu____1896 =
                 let uu____1899 = comp_to_typ c in new_uvar env' uu____1899 in
               bind uu____1896
                 (fun u  ->
                    let lb =
                      let uu____1916 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.goal_ty FStar_Parser_Const.effect_Tot_lid
                        uu____1916 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1920 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1920 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.witness).FStar_Syntax_Syntax.pos in
                        (FStar_Util.print_string "calling teq_nosmt\n";
                         (let res = trysolve goal tm in
                          if res
                          then
                            let uu____1958 =
                              let uu____1961 =
                                let uu___102_1962 = goal in
                                let uu____1963 = bnorm env' u in
                                let uu____1964 =
                                  let uu____1965 = comp_to_typ c in
                                  bnorm env' uu____1965 in
                                {
                                  context = env';
                                  witness = uu____1963;
                                  goal_ty = uu____1964;
                                  opts = (uu___102_1962.opts);
                                  is_guard = (uu___102_1962.is_guard)
                                } in
                              replace_cur uu____1961 in
                            bind uu____1958
                              (fun uu____1972  ->
                                 let uu____1973 =
                                   let uu____1978 =
                                     FStar_Syntax_Syntax.mk_binder bv in
                                   (uu____1978, b) in
                                 ret uu____1973)
                          else fail "intro_rec: unification failed"))))
        | FStar_Pervasives_Native.None  ->
            let uu____1992 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1992))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2017 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2017 in
         let w = normalize steps goal.context goal.witness in
         let t = normalize steps goal.context goal.goal_ty in
         replace_cur
           (let uu___103_2024 = goal in
            {
              context = (uu___103_2024.context);
              witness = w;
              goal_ty = t;
              opts = (uu___103_2024.opts);
              is_guard = (uu___103_2024.is_guard)
            }))
let norm_term:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun s  ->
    fun t  ->
      bind get
        (fun ps  ->
           let steps =
             let uu____2048 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____2048 in
           let t1 = normalize steps ps.main_context t in ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2063 =
           try
             let uu____2091 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2091
           with
           | e ->
               let uu____2118 = FStar_Syntax_Print.term_to_string t in
               let uu____2119 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2118
                 uu____2119 in
         bind uu____2063
           (fun uu____2137  ->
              match uu____2137 with
              | (t1,typ,guard) ->
                  let uu____2149 =
                    let uu____2150 =
                      let uu____2151 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2151 in
                    Prims.op_Negation uu____2150 in
                  if uu____2149
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2155 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2155
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2160 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2161 =
                          let uu____2162 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2162 in
                        let uu____2163 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2160 uu____2161 uu____2163))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____2172 = __exact t in focus uu____2172
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2186 =
           try
             let uu____2214 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2214
           with
           | e ->
               let uu____2241 = FStar_Syntax_Print.term_to_string t in
               let uu____2242 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2241
                 uu____2242 in
         bind uu____2186
           (fun uu____2260  ->
              match uu____2260 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2278 =
                       let uu____2279 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2279 in
                     if uu____2278
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2283 =
                          let uu____2292 =
                            let uu____2301 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2301.FStar_Syntax_Syntax.effect_args in
                          match uu____2292 with
                          | pre::post::uu____2312 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2353 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2283 with
                        | (pre,post) ->
                            let uu____2382 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2382
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2387  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2389 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2390 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2391 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2389 uu____2390 uu____2391)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.is_guard
      then false
      else
        (let free_uvars =
           let uu____2404 =
             let uu____2411 = FStar_Syntax_Free.uvars g.goal_ty in
             FStar_Util.set_elements uu____2411 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2404 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2438 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2458 =
               let uu____2463 = __exact tm in trytac uu____2463 in
             bind uu____2458
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2476 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2476 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2506 =
                             let uu____2507 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2507 in
                           if uu____2506
                           then fail "apply: not total codomain"
                           else
                             (let uu____2511 =
                                new_uvar goal.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2511
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2531 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2531 in
                                   let uu____2532 = __apply uopt tm' typ' in
                                   bind uu____2532
                                     (fun uu____2539  ->
                                        let uu____2540 =
                                          let uu____2541 =
                                            let uu____2544 =
                                              let uu____2545 =
                                                FStar_Syntax_Util.head_and_args
                                                  u in
                                              FStar_Pervasives_Native.fst
                                                uu____2545 in
                                            FStar_Syntax_Subst.compress
                                              uu____2544 in
                                          uu____2541.FStar_Syntax_Syntax.n in
                                        match uu____2540 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2573) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2601 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2601
                                                 then ret ()
                                                 else
                                                   (let uu____2605 =
                                                      let uu____2608 =
                                                        let uu___108_2609 =
                                                          goal in
                                                        let uu____2610 =
                                                          bnorm goal.context
                                                            u in
                                                        let uu____2611 =
                                                          bnorm goal.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          context =
                                                            (uu___108_2609.context);
                                                          witness =
                                                            uu____2610;
                                                          goal_ty =
                                                            uu____2611;
                                                          opts =
                                                            (uu___108_2609.opts);
                                                          is_guard = false
                                                        } in
                                                      [uu____2608] in
                                                    add_goals uu____2605))
                                        | uu____2612 -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2670 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2670 with
           | (tm1,typ,guard) ->
               let uu____2682 =
                 let uu____2685 =
                   let uu____2688 = __apply uopt tm1 typ in
                   bind uu____2688
                     (fun uu____2692  ->
                        add_goal_from_guard goal.context guard goal.opts) in
                 focus uu____2685 in
               let uu____2693 =
                 let uu____2696 = FStar_Syntax_Print.term_to_string tm1 in
                 let uu____2697 = FStar_Syntax_Print.term_to_string typ in
                 let uu____2698 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2696 uu____2697 uu____2698 in
               try_unif uu____2682 uu____2693)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2707 =
      let is_unit_t t =
        let uu____2714 =
          let uu____2715 = FStar_Syntax_Subst.compress t in
          uu____2715.FStar_Syntax_Syntax.n in
        match uu____2714 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2719 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2729 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2729 with
           | (tm1,t,guard) ->
               let uu____2741 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2741 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2771 =
                         FStar_List.fold_left
                           (fun uu____2817  ->
                              fun uu____2818  ->
                                match (uu____2817, uu____2818) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2921 = is_unit_t b_t in
                                    if uu____2921
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2959 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____2959 with
                                       | (u,uu____2989,g_u) ->
                                           let uu____3003 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____3003,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2771 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3073 =
                             let uu____3082 =
                               let uu____3091 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3091.FStar_Syntax_Syntax.effect_args in
                             match uu____3082 with
                             | pre::post::uu____3102 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3143 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3073 with
                            | (pre,post) ->
                                let uu____3172 =
                                  let uu____3173 =
                                    let uu____3174 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Rel.teq_nosmt
                                      goal.context uu____3174 goal.goal_ty in
                                  Prims.op_Negation uu____3173 in
                                if uu____3172
                                then
                                  let uu____3177 =
                                    FStar_Syntax_Print.term_to_string tm1 in
                                  let uu____3178 =
                                    let uu____3179 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_Syntax_Print.term_to_string
                                      uu____3179 in
                                  let uu____3180 =
                                    FStar_Syntax_Print.term_to_string
                                      goal.goal_ty in
                                  fail3
                                    "apply: Cannot instantiate lemma %s (with postcondition %s) to match goal (%s)"
                                    uu____3177 uu____3178 uu____3180
                                else
                                  (let solution =
                                     let uu____3183 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.context uu____3183 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____3251  ->
                                             match uu____3251 with
                                             | (uu____3264,uu____3265,uu____3266,tm2,uu____3268,uu____3269)
                                                 ->
                                                 let uu____3270 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3270 with
                                                  | (hd1,uu____3286) ->
                                                      let uu____3307 =
                                                        let uu____3308 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3308.FStar_Syntax_Syntax.n in
                                                      (match uu____3307 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3311 -> true
                                                       | uu____3328 -> false)))) in
                                   solve goal solution;
                                   (let uu____3330 = add_implicits implicits1 in
                                    bind uu____3330
                                      (fun uu____3334  ->
                                         bind dismiss
                                           (fun uu____3343  ->
                                              let is_free_uvar uv t1 =
                                                let free_uvars =
                                                  let uu____3354 =
                                                    let uu____3361 =
                                                      FStar_Syntax_Free.uvars
                                                        t1 in
                                                    FStar_Util.set_elements
                                                      uu____3361 in
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.fst
                                                    uu____3354 in
                                                FStar_List.existsML
                                                  (fun u  ->
                                                     FStar_Syntax_Unionfind.equiv
                                                       u uv) free_uvars in
                                              let appears uv goals =
                                                FStar_List.existsML
                                                  (fun g'  ->
                                                     is_free_uvar uv
                                                       g'.goal_ty) goals in
                                              let checkone t1 goals =
                                                let uu____3402 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t1 in
                                                match uu____3402 with
                                                | (hd1,uu____3418) ->
                                                    (match hd1.FStar_Syntax_Syntax.n
                                                     with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         (uv,uu____3440) ->
                                                         appears uv goals
                                                     | uu____3465 -> false) in
                                              let sub_goals =
                                                FStar_All.pipe_right
                                                  implicits1
                                                  (FStar_List.map
                                                     (fun uu____3507  ->
                                                        match uu____3507 with
                                                        | (_msg,_env,_uvar,term,typ,uu____3525)
                                                            ->
                                                            let uu___111_3526
                                                              = goal in
                                                            let uu____3527 =
                                                              bnorm
                                                                goal.context
                                                                term in
                                                            let uu____3528 =
                                                              bnorm
                                                                goal.context
                                                                typ in
                                                            {
                                                              context =
                                                                (uu___111_3526.context);
                                                              witness =
                                                                uu____3527;
                                                              goal_ty =
                                                                uu____3528;
                                                              opts =
                                                                (uu___111_3526.opts);
                                                              is_guard =
                                                                (uu___111_3526.is_guard)
                                                            })) in
                                              let rec filter' f xs =
                                                match xs with
                                                | [] -> []
                                                | x::xs1 ->
                                                    let uu____3566 = f x xs1 in
                                                    if uu____3566
                                                    then
                                                      let uu____3569 =
                                                        filter' f xs1 in
                                                      x :: uu____3569
                                                    else filter' f xs1 in
                                              let sub_goals1 =
                                                filter'
                                                  (fun g  ->
                                                     fun goals  ->
                                                       let uu____3583 =
                                                         checkone g.witness
                                                           goals in
                                                       Prims.op_Negation
                                                         uu____3583)
                                                  sub_goals in
                                              let uu____3584 =
                                                add_goal_from_guard
                                                  goal.context guard
                                                  goal.opts in
                                              bind uu____3584
                                                (fun uu____3589  ->
                                                   let uu____3590 =
                                                     add_irrelevant_goal
                                                       goal.context pre
                                                       goal.opts in
                                                   bind uu____3590
                                                     (fun uu____3595  ->
                                                        let uu____3596 =
                                                          trytac trivial in
                                                        bind uu____3596
                                                          (fun uu____3604  ->
                                                             add_goals
                                                               sub_goals1))))))))))) in
    focus uu____2707
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3623 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3623 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3633::(e1,uu____3635)::(e2,uu____3637)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3696 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3719 = destruct_eq' typ in
    match uu____3719 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3749 = FStar_Syntax_Util.un_squash typ in
        (match uu____3749 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3782 =
           FStar_All.pipe_left mlog
             (fun uu____3792  ->
                let uu____3793 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3794 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3793
                  uu____3794) in
         bind uu____3782
           (fun uu____3802  ->
              let uu____3803 =
                let uu____3810 =
                  let uu____3811 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3811 in
                destruct_eq uu____3810 in
              match uu____3803 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3828 =
                    let uu____3829 = FStar_Syntax_Subst.compress x in
                    uu____3829.FStar_Syntax_Syntax.n in
                  (match uu____3828 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___112_3836 = goal in
                         let uu____3837 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3838 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___112_3836.context);
                           witness = uu____3837;
                           goal_ty = uu____3838;
                           opts = (uu___112_3836.opts);
                           is_guard = (uu___112_3836.is_guard)
                         } in
                       replace_cur goal1
                   | uu____3839 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3840 -> fail "Not an equality hypothesis"))
let subst_goal:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let rec alpha e =
            let uu____3871 = FStar_TypeChecker_Env.pop_bv e in
            match uu____3871 with
            | FStar_Pervasives_Native.None  -> e
            | FStar_Pervasives_Native.Some (bv,e') ->
                if FStar_Syntax_Syntax.bv_eq bv b1
                then FStar_TypeChecker_Env.push_bv e' b2
                else
                  (let uu____3889 = alpha e' in
                   let uu____3890 =
                     let uu___113_3891 = bv in
                     let uu____3892 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___113_3891.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___113_3891.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3892
                     } in
                   FStar_TypeChecker_Env.push_bv uu____3889 uu____3890) in
          let c = alpha g.context in
          let w = FStar_Syntax_Subst.subst s g.witness in
          let t = FStar_Syntax_Subst.subst s g.goal_ty in
          let uu___114_3898 = g in
          {
            context = c;
            witness = w;
            goal_ty = t;
            opts = (uu___114_3898.opts);
            is_guard = (uu___114_3898.is_guard)
          }
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3919 = b in
           match uu____3919 with
           | (bv,uu____3923) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___115_3927 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___115_3927.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___115_3927.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3931 =
                   let uu____3932 =
                     let uu____3939 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3939) in
                   FStar_Syntax_Syntax.NT uu____3932 in
                 [uu____3931] in
               let uu____3940 = subst_goal bv bv' s1 goal in
               replace_cur uu____3940)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3946 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3946 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3968 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3968 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___116_4002 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___116_4002.opts);
                is_guard = (uu___116_4002.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4014 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4014 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4035 = FStar_Syntax_Print.bv_to_string x in
               let uu____4036 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4035 uu____4036
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4043 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____4043 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____4065 = FStar_Util.set_mem x fns_ty in
           if uu____4065
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4069 = new_uvar env' goal.goal_ty in
              bind uu____4069
                (fun u  ->
                   let uu____4075 =
                     let uu____4076 = trysolve goal u in
                     Prims.op_Negation uu____4076 in
                   if uu____4075
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___117_4081 = goal in
                        let uu____4082 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____4082;
                          goal_ty = (uu___117_4081.goal_ty);
                          opts = (uu___117_4081.opts);
                          is_guard = (uu___117_4081.is_guard)
                        } in
                      bind dismiss (fun uu____4084  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4096 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4096 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4120  ->
                    let uu____4121 = clear b in
                    bind uu____4121
                      (fun uu____4125  ->
                         bind intro (fun uu____4127  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___118_4144 = g in
           {
             context = ctx';
             witness = (uu___118_4144.witness);
             goal_ty = (uu___118_4144.goal_ty);
             opts = (uu___118_4144.opts);
             is_guard = (uu___118_4144.is_guard)
           } in
         bind dismiss (fun uu____4146  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___119_4163 = g in
           {
             context = ctx';
             witness = (uu___119_4163.witness);
             goal_ty = (uu___119_4163.goal_ty);
             opts = (uu___119_4163.opts);
             is_guard = (uu___119_4163.is_guard)
           } in
         bind dismiss (fun uu____4165  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4207 = f x in
          bind uu____4207
            (fun y  ->
               let uu____4215 = mapM f xs in
               bind uu____4215 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4261 = FStar_Syntax_Subst.compress t in
          uu____4261.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4296 = ff hd1 in
              bind uu____4296
                (fun hd2  ->
                   let fa uu____4316 =
                     match uu____4316 with
                     | (a,q) ->
                         let uu____4329 = ff a in
                         bind uu____4329 (fun a1  -> ret (a1, q)) in
                   let uu____4342 = mapM fa args in
                   bind uu____4342
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4402 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4402 with
               | (bs1,t') ->
                   let uu____4411 =
                     let uu____4414 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4414 t' in
                   bind uu____4411
                     (fun t''  ->
                        let uu____4418 =
                          let uu____4419 =
                            let uu____4436 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4437 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4436, uu____4437, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4419 in
                        ret uu____4418))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4458 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___120_4462 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___120_4462.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___120_4462.FStar_Syntax_Syntax.vars)
                }))
let pointwise_rec:
  proofstate ->
    Prims.unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____4491 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4491 with
            | (t1,lcomp,g) ->
                let uu____4503 =
                  let uu____4504 = FStar_TypeChecker_Rel.is_trivial g in
                  Prims.op_Negation uu____4504 in
                if uu____4503
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4511 = new_uvar env typ in
                   bind uu____4511
                     (fun ut  ->
                        log ps
                          (fun uu____4522  ->
                             let uu____4523 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4524 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4523 uu____4524);
                        (let uu____4525 =
                           let uu____4528 =
                             let uu____4529 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4529 typ t1 ut in
                           add_irrelevant_goal env uu____4528 opts in
                         bind uu____4525
                           (fun uu____4532  ->
                              let uu____4533 =
                                bind tau
                                  (fun uu____4538  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4533))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4559 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4559 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4596  ->
                   let uu____4597 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4597);
              bind dismiss_all
                (fun uu____4600  ->
                   let uu____4601 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4601
                     (fun gt'  ->
                        log ps
                          (fun uu____4611  ->
                             let uu____4612 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4612);
                        (let uu____4613 = push_goals gs in
                         bind uu____4613
                           (fun uu____4617  ->
                              add_goals
                                [(let uu___121_4619 = g in
                                  {
                                    context = (uu___121_4619.context);
                                    witness = (uu___121_4619.witness);
                                    goal_ty = gt';
                                    opts = (uu___121_4619.opts);
                                    is_guard = (uu___121_4619.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4639 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4639 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4651 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4651 with
            | (hd1,args) ->
                let uu____4684 =
                  let uu____4697 =
                    let uu____4698 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4698.FStar_Syntax_Syntax.n in
                  (uu____4697, args) in
                (match uu____4684 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4712::(l,uu____4714)::(r,uu____4716)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4763 =
                       let uu____4764 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4764 in
                     if uu____4763
                     then
                       let uu____4767 = FStar_Syntax_Print.term_to_string l in
                       let uu____4768 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4767 uu____4768
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4772) ->
                     let uu____4789 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4789))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4797 = new_uvar g.context g.goal_ty in
       bind uu____4797
         (fun u  ->
            let g' =
              let uu___122_4804 = g in
              {
                context = (uu___122_4804.context);
                witness = u;
                goal_ty = (uu___122_4804.goal_ty);
                opts = (uu___122_4804.opts);
                is_guard = (uu___122_4804.is_guard)
              } in
            bind dismiss
              (fun uu____4807  ->
                 let uu____4808 =
                   let uu____4811 =
                     let uu____4812 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4812 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____4811 g.opts in
                 bind uu____4808
                   (fun uu____4815  ->
                      let uu____4816 = add_goals [g'] in
                      bind uu____4816 (fun uu____4820  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___123_4837 = ps in
              {
                main_context = (uu___123_4837.main_context);
                main_goal = (uu___123_4837.main_goal);
                all_implicits = (uu___123_4837.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___123_4837.smt_goals)
              })
       | uu____4838 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___124_4853 = ps in
              {
                main_context = (uu___124_4853.main_context);
                main_goal = (uu___124_4853.main_goal);
                all_implicits = (uu___124_4853.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___124_4853.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4860 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4902 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4902 with
         | (t1,typ,guard) ->
             let uu____4918 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4918 with
              | (hd1,args) ->
                  let uu____4961 =
                    let uu____4974 =
                      let uu____4975 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4975.FStar_Syntax_Syntax.n in
                    (uu____4974, args) in
                  (match uu____4961 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4994)::(q,uu____4996)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.or_lid
                       ->
                       let v_p =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None p in
                       let v_q =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None q in
                       let g1 =
                         let uu___125_5034 = g in
                         let uu____5035 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____5035;
                           witness = (uu___125_5034.witness);
                           goal_ty = (uu___125_5034.goal_ty);
                           opts = (uu___125_5034.opts);
                           is_guard = (uu___125_5034.is_guard)
                         } in
                       let g2 =
                         let uu___126_5037 = g in
                         let uu____5038 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____5038;
                           witness = (uu___126_5037.witness);
                           goal_ty = (uu___126_5037.goal_ty);
                           opts = (uu___126_5037.opts);
                           is_guard = (uu___126_5037.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5045  ->
                            let uu____5046 = add_goals [g1; g2] in
                            bind uu____5046
                              (fun uu____5055  ->
                                 let uu____5056 =
                                   let uu____5061 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5062 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5061, uu____5062) in
                                 ret uu____5056))
                   | uu____5067 ->
                       let uu____5080 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____5080)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5103 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5103);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___127_5110 = g in
                 {
                   context = (uu___127_5110.context);
                   witness = (uu___127_5110.witness);
                   goal_ty = (uu___127_5110.goal_ty);
                   opts = opts';
                   is_guard = (uu___127_5110.is_guard)
                 } in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
let cur_env: env tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.context)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.goal_ty)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.witness)
let unquote:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ty  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let env = FStar_TypeChecker_Env.set_expected_typ goal.context ty in
           let uu____5151 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____5151 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5180 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5186 =
              let uu____5187 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5187 in
            new_uvar env uu____5186 in
      bind uu____5180
        (fun typ  ->
           let uu____5199 = new_uvar env typ in
           bind uu____5199 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5219 =
             FStar_TypeChecker_Rel.teq_nosmt ps.main_context t1 t2 in
           ret uu____5219)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5239  ->
             let uu____5240 = FStar_Options.unsafe_tactic_exec () in
             if uu____5240
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5246  -> fun uu____5247  -> false) in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let goal_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (goal,FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5269 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5269 with
      | (u,uu____5287,g_u) ->
          let g =
            let uu____5302 = FStar_Options.peek () in
            {
              context = env;
              witness = u;
              goal_ty = typ;
              opts = uu____5302;
              is_guard = false
            } in
          (g, g_u)
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (proofstate,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5319 = goal_of_goal_ty env typ in
      match uu____5319 with
      | (g,g_u) ->
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, (g.witness))