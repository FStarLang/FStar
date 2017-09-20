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
  opts: FStar_Options.optionstate;
  is_guard: Prims.bool;}
let __proj__Mkgoal__item__context: goal -> env =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__context
let __proj__Mkgoal__item__witness: goal -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__witness
let __proj__Mkgoal__item__goal_ty: goal -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__goal_ty
let __proj__Mkgoal__item__opts: goal -> FStar_Options.optionstate =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__opts
let __proj__Mkgoal__item__is_guard: goal -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__is_guard
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
    match projectee with | Success _0 -> true | uu____228 -> false
let __proj__Success__item___0:
  'a . 'a result -> ('a,proofstate) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: 'a . 'a result -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____274 -> false
let __proj__Failed__item___0:
  'a . 'a result -> (Prims.string,proofstate) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____309 -> true | uu____310 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____318 -> uu____318
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let __proj__Mktac__item__tac_f: 'a . 'a tac -> proofstate -> 'a result =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
let mk_tac: 'a . (proofstate -> 'a result) -> 'a tac =
  fun f  -> { tac_f = f }
let run: 'Auu____382 . 'Auu____382 tac -> proofstate -> 'Auu____382 result =
  fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac = fun x  -> mk_tac (fun p  -> Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____449 = run t1 p in
           match uu____449 with
           | Success (a,q) -> let uu____456 = t2 a in run uu____456 q
           | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____468 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____468
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.context g.witness in
    let t = bnorm g.context g.goal_ty in
    let uu____471 = FStar_TypeChecker_Normalize.term_to_string g.context w in
    let uu____472 = FStar_TypeChecker_Normalize.term_to_string g.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____471 uu____472
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____485 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____485
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____498 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____498
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____515 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____515
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____521) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____531) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____545 =
      let uu____550 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____550 in
    match uu____545 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____556 -> false
let dump_goal: 'Auu____567 . 'Auu____567 -> goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____577 = goal_to_string goal in tacprint uu____577
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____587 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____591 = FStar_List.hd ps.goals in dump_goal ps uu____591))
let ps_to_string:
  (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> Prims.string =
  fun uu____599  ->
    match uu____599 with
    | (msg,ps) ->
        let uu____606 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
        let uu____607 =
          let uu____608 = FStar_List.map goal_to_string ps.goals in
          FStar_String.concat "\n" uu____608 in
        let uu____611 =
          FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
        let uu____612 =
          let uu____613 = FStar_List.map goal_to_string ps.smt_goals in
          FStar_String.concat "\n" uu____613 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____606 uu____607 uu____611 uu____612
let goal_to_json: goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____621 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____621 FStar_Syntax_Print.binders_to_json in
    let uu____622 =
      let uu____629 =
        let uu____636 =
          let uu____641 =
            let uu____642 =
              let uu____649 =
                let uu____654 =
                  let uu____655 =
                    FStar_TypeChecker_Normalize.term_to_string g.context
                      g.witness in
                  FStar_Util.JsonStr uu____655 in
                ("witness", uu____654) in
              let uu____656 =
                let uu____663 =
                  let uu____668 =
                    let uu____669 =
                      FStar_TypeChecker_Normalize.term_to_string g.context
                        g.goal_ty in
                    FStar_Util.JsonStr uu____669 in
                  ("type", uu____668) in
                [uu____663] in
              uu____649 :: uu____656 in
            FStar_Util.JsonAssoc uu____642 in
          ("goal", uu____641) in
        [uu____636] in
      ("hyps", g_binders) :: uu____629 in
    FStar_Util.JsonAssoc uu____622
let ps_to_json:
  (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____701  ->
    match uu____701 with
    | (msg,ps) ->
        let uu____708 =
          let uu____715 =
            let uu____722 =
              let uu____727 =
                let uu____728 = FStar_List.map goal_to_json ps.goals in
                FStar_Util.JsonList uu____728 in
              ("goals", uu____727) in
            let uu____731 =
              let uu____738 =
                let uu____743 =
                  let uu____744 = FStar_List.map goal_to_json ps.smt_goals in
                  FStar_Util.JsonList uu____744 in
                ("smt-goals", uu____743) in
              [uu____738] in
            uu____722 :: uu____731 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____715 in
        FStar_Util.JsonAssoc uu____708
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____773  ->
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
      let uu____833 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____833 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____855 =
              let uu____858 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____858 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____855);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____898 . Prims.string -> 'Auu____898 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____909 =
            FStar_TypeChecker_Env.debug ps.main_context
              (FStar_Options.Other "TacFail") in
          if uu____909
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         Failed (msg, ps))
let fail1: 'Auu____917 . Prims.string -> Prims.string -> 'Auu____917 tac =
  fun msg  ->
    fun x  -> let uu____928 = FStar_Util.format1 msg x in fail uu____928
let fail2:
  'Auu____937 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____937 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____952 = FStar_Util.format2 msg x y in fail uu____952
let fail3:
  'Auu____963 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____963 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____982 = FStar_Util.format3 msg x y z in fail uu____982
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____1010 = run t ps in
         match uu____1010 with
         | Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              Success ((FStar_Pervasives_Native.Some a), q))
         | Failed (uu____1024,uu____1025) ->
             (FStar_Syntax_Unionfind.rollback tx;
              Success (FStar_Pervasives_Native.None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____1040  -> Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____1058 -> false
let trysolve: goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  -> fun solution  -> do_unify goal.context solution goal.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____1072 =
         let uu___88_1073 = p in
         let uu____1074 = FStar_List.tl p.goals in
         {
           main_context = (uu___88_1073.main_context);
           main_goal = (uu___88_1073.main_goal);
           all_implicits = (uu___88_1073.all_implicits);
           goals = uu____1074;
           smt_goals = (uu___88_1073.smt_goals)
         } in
       set uu____1072)
let solve: goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____1089 = trysolve goal solution in
      if uu____1089
      then dismiss
      else
        (let uu____1093 =
           let uu____1094 =
             FStar_TypeChecker_Normalize.term_to_string goal.context solution in
           let uu____1095 =
             FStar_TypeChecker_Normalize.term_to_string goal.context
               goal.witness in
           let uu____1096 =
             FStar_TypeChecker_Normalize.term_to_string goal.context
               goal.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____1094
             uu____1095 uu____1096 in
         fail uu____1093)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___89_1103 = p in
          {
            main_context = (uu___89_1103.main_context);
            main_goal = (uu___89_1103.main_goal);
            all_implicits = (uu___89_1103.all_implicits);
            goals = [];
            smt_goals = (uu___89_1103.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_1120 = p in
            {
              main_context = (uu___90_1120.main_context);
              main_goal = (uu___90_1120.main_goal);
              all_implicits = (uu___90_1120.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___90_1120.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_1137 = p in
            {
              main_context = (uu___91_1137.main_context);
              main_goal = (uu___91_1137.main_goal);
              all_implicits = (uu___91_1137.all_implicits);
              goals = (uu___91_1137.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1154 = p in
            {
              main_context = (uu___92_1154.main_context);
              main_goal = (uu___92_1154.main_goal);
              all_implicits = (uu___92_1154.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___92_1154.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___93_1171 = p in
            {
              main_context = (uu___93_1171.main_context);
              main_goal = (uu___93_1171.main_goal);
              all_implicits = (uu___93_1171.all_implicits);
              goals = (uu___93_1171.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1181  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___94_1194 = p in
            {
              main_context = (uu___94_1194.main_context);
              main_goal = (uu___94_1194.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___94_1194.goals);
              smt_goals = (uu___94_1194.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____1219 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1219 with
      | (u,uu____1235,g_u) ->
          let uu____1249 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1249 (fun uu____1253  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1258 = FStar_Syntax_Util.un_squash t in
    match uu____1258 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1268 =
          let uu____1269 = FStar_Syntax_Subst.compress t' in
          uu____1269.FStar_Syntax_Syntax.n in
        (match uu____1268 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1273 -> false)
    | uu____1274 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1283 = FStar_Syntax_Util.un_squash t in
    match uu____1283 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1293 =
          let uu____1294 = FStar_Syntax_Subst.compress t' in
          uu____1294.FStar_Syntax_Syntax.n in
        (match uu____1293 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1298 -> false)
    | uu____1299 -> false
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
        let uu____1333 = new_uvar env typ in
        bind uu____1333
          (fun u  ->
             let goal =
               {
                 context = env;
                 witness = u;
                 goal_ty = typ;
                 opts;
                 is_guard = false
               } in
             ret goal)
let add_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let uu____1356 = mk_irrelevant_goal env phi opts in
        bind uu____1356 (fun goal  -> add_goals [goal])
let istrivial: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac;
        FStar_TypeChecker_Normalize.Unmeta] in
      let t1 = normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1378 = istrivial goal.context goal.goal_ty in
       if uu____1378
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1382 =
            FStar_TypeChecker_Normalize.term_to_string goal.context
              goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1382))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1399 =
          let uu____1400 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1400.FStar_TypeChecker_Env.guard_f in
        match uu____1399 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1404 = istrivial e f in
            if uu____1404
            then ret ()
            else
              (let uu____1408 = mk_irrelevant_goal e f opts in
               bind uu____1408
                 (fun goal  ->
                    let goal1 =
                      let uu___95_1415 = goal in
                      {
                        context = (uu___95_1415.context);
                        witness = (uu___95_1415.witness);
                        goal_ty = (uu___95_1415.goal_ty);
                        opts = (uu___95_1415.opts);
                        is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1421 = is_irrelevant g in
       if uu____1421
       then bind dismiss (fun uu____1425  -> add_smt_goals [g])
       else
         (let uu____1427 =
            FStar_TypeChecker_Normalize.term_to_string g.context g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1427))
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
             let uu____1473 =
               try
                 let uu____1507 = FStar_List.splitAt n1 p.goals in
                 ret uu____1507
               with | uu____1537 -> fail "divide: not enough goals" in
             bind uu____1473
               (fun uu____1564  ->
                  match uu____1564 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___96_1590 = p in
                        {
                          main_context = (uu___96_1590.main_context);
                          main_goal = (uu___96_1590.main_goal);
                          all_implicits = (uu___96_1590.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___97_1592 = p in
                        {
                          main_context = (uu___97_1592.main_context);
                          main_goal = (uu___97_1592.main_goal);
                          all_implicits = (uu___97_1592.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1593 = set lp in
                      bind uu____1593
                        (fun uu____1601  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1615 = set rp in
                                     bind uu____1615
                                       (fun uu____1623  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___98_1639 = p in
                                                      {
                                                        main_context =
                                                          (uu___98_1639.main_context);
                                                        main_goal =
                                                          (uu___98_1639.main_goal);
                                                        all_implicits =
                                                          (uu___98_1639.all_implicits);
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
                                                    let uu____1640 = set p' in
                                                    bind uu____1640
                                                      (fun uu____1648  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1668 = divide (Prims.parse_int "1") f idtac in
    bind uu____1668
      (fun uu____1681  -> match uu____1681 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1716::uu____1717 ->
             let uu____1720 =
               let uu____1729 = map tau in
               divide (Prims.parse_int "1") tau uu____1729 in
             bind uu____1720
               (fun uu____1747  ->
                  match uu____1747 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1786 =
        bind t1
          (fun uu____1791  ->
             let uu____1792 = map t2 in
             bind uu____1792 (fun uu____1800  -> ret ())) in
      focus uu____1786
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1811 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1811 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1826 =
             let uu____1827 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1827 in
           if uu____1826
           then fail "Codomain is effectful"
           else
             (let env' = FStar_TypeChecker_Env.push_binders goal.context [b] in
              let typ' = comp_to_typ c in
              let uu____1833 = new_uvar env' typ' in
              bind uu____1833
                (fun u  ->
                   let uu____1840 =
                     let uu____1841 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1841 in
                   if uu____1840
                   then
                     let uu____1844 =
                       let uu____1847 =
                         let uu___101_1848 = goal in
                         let uu____1849 = bnorm env' u in
                         let uu____1850 = bnorm env' typ' in
                         {
                           context = env';
                           witness = uu____1849;
                           goal_ty = uu____1850;
                           opts = (uu___101_1848.opts);
                           is_guard = (uu___101_1848.is_guard)
                         } in
                       replace_cur uu____1847 in
                     bind uu____1844 (fun uu____1852  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1858 =
             FStar_TypeChecker_Normalize.term_to_string goal.context
               goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1858)
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
       (let uu____1879 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1879 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1898 =
              let uu____1899 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1899 in
            if uu____1898
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None goal.goal_ty in
               let bs =
                 let uu____1915 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1915; b] in
               let env' = FStar_TypeChecker_Env.push_binders goal.context bs in
               let uu____1917 =
                 let uu____1920 = comp_to_typ c in new_uvar env' uu____1920 in
               bind uu____1917
                 (fun u  ->
                    let lb =
                      let uu____1936 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.goal_ty FStar_Parser_Const.effect_Tot_lid
                        uu____1936 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1940 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1940 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1977 =
                            let uu____1980 =
                              let uu___102_1981 = goal in
                              let uu____1982 = bnorm env' u in
                              let uu____1983 =
                                let uu____1984 = comp_to_typ c in
                                bnorm env' uu____1984 in
                              {
                                context = env';
                                witness = uu____1982;
                                goal_ty = uu____1983;
                                opts = (uu___102_1981.opts);
                                is_guard = (uu___102_1981.is_guard)
                              } in
                            replace_cur uu____1980 in
                          bind uu____1977
                            (fun uu____1991  ->
                               let uu____1992 =
                                 let uu____1997 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1997, b) in
                               ret uu____1992)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2011 =
              FStar_TypeChecker_Normalize.term_to_string goal.context
                goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2011))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2036 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2036 in
         let w = normalize steps goal.context goal.witness in
         let t = normalize steps goal.context goal.goal_ty in
         replace_cur
           (let uu___103_2043 = goal in
            {
              context = (uu___103_2043.context);
              witness = w;
              goal_ty = t;
              opts = (uu___103_2043.opts);
              is_guard = (uu___103_2043.is_guard)
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
             let uu____2067 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____2067 in
           let t1 = normalize steps ps.main_context t in ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2082 =
           try
             let uu____2110 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2110
           with
           | e ->
               let uu____2137 = FStar_Syntax_Print.term_to_string t in
               let uu____2138 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2137
                 uu____2138 in
         bind uu____2082
           (fun uu____2156  ->
              match uu____2156 with
              | (t1,typ,guard) ->
                  let uu____2168 =
                    let uu____2169 =
                      let uu____2170 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2170 in
                    Prims.op_Negation uu____2169 in
                  if uu____2168
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2174 = do_unify goal.context typ goal.goal_ty in
                     if uu____2174
                     then solve goal t1
                     else
                       (let uu____2178 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.context t1 in
                        let uu____2179 =
                          let uu____2180 = bnorm goal.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.context uu____2180 in
                        let uu____2181 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.context goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2178 uu____2179 uu____2181))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____2190 = __exact t in focus uu____2190
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2204 =
           try
             let uu____2232 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2232
           with
           | e ->
               let uu____2259 = FStar_Syntax_Print.term_to_string t in
               let uu____2260 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2259
                 uu____2260 in
         bind uu____2204
           (fun uu____2278  ->
              match uu____2278 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2296 =
                       let uu____2297 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2297 in
                     if uu____2296
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2301 =
                          let uu____2310 =
                            let uu____2319 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2319.FStar_Syntax_Syntax.effect_args in
                          match uu____2310 with
                          | pre::post::uu____2330 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2371 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2301 with
                        | (pre,post) ->
                            let uu____2400 =
                              do_unify goal.context post goal.goal_ty in
                            if uu____2400
                            then
                              let uu____2403 = solve goal t1 in
                              bind uu____2403
                                (fun uu____2407  ->
                                   add_irrelevant_goal goal.context pre
                                     goal.opts)
                            else
                              (let uu____2409 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.context t1 in
                               let uu____2410 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.context post in
                               let uu____2411 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.context goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2409 uu____2410 uu____2411)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.is_guard
      then false
      else
        (let free_uvars =
           let uu____2424 =
             let uu____2431 = FStar_Syntax_Free.uvars g.goal_ty in
             FStar_Util.set_elements uu____2431 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2424 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2458 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2478 =
               let uu____2483 = __exact tm in trytac uu____2483 in
             bind uu____2478
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2496 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2496 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2526 =
                             let uu____2527 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2527 in
                           if uu____2526
                           then fail "apply: not total codomain"
                           else
                             (let uu____2531 =
                                new_uvar goal.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2531
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2551 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2551 in
                                   let uu____2552 = __apply uopt tm' typ' in
                                   bind uu____2552
                                     (fun uu____2560  ->
                                        let u1 = bnorm goal.context u in
                                        let uu____2562 =
                                          let uu____2563 =
                                            let uu____2566 =
                                              let uu____2567 =
                                                FStar_Syntax_Util.head_and_args
                                                  u1 in
                                              FStar_Pervasives_Native.fst
                                                uu____2567 in
                                            FStar_Syntax_Subst.compress
                                              uu____2566 in
                                          uu____2563.FStar_Syntax_Syntax.n in
                                        match uu____2562 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2595) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2623 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2623
                                                 then ret ()
                                                 else
                                                   (let uu____2627 =
                                                      let uu____2630 =
                                                        let uu___108_2631 =
                                                          goal in
                                                        let uu____2632 =
                                                          bnorm goal.context
                                                            u1 in
                                                        let uu____2633 =
                                                          bnorm goal.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          context =
                                                            (uu___108_2631.context);
                                                          witness =
                                                            uu____2632;
                                                          goal_ty =
                                                            uu____2633;
                                                          opts =
                                                            (uu___108_2631.opts);
                                                          is_guard = false
                                                        } in
                                                      [uu____2630] in
                                                    add_goals uu____2627))
                                        | t ->
                                            ((let uu____2636 =
                                                FStar_Syntax_Print.term_to_string
                                                  u1 in
                                              FStar_Util.print1
                                                "__apply: uvar was instantiated to %s\n"
                                                uu____2636);
                                             ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2694 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2694 with
           | (tm1,typ,guard) ->
               let uu____2706 =
                 let uu____2709 =
                   let uu____2712 = __apply uopt tm1 typ in
                   bind uu____2712
                     (fun uu____2716  ->
                        add_goal_from_guard goal.context guard goal.opts) in
                 focus uu____2709 in
               let uu____2717 =
                 let uu____2720 =
                   FStar_TypeChecker_Normalize.term_to_string goal.context
                     tm1 in
                 let uu____2721 =
                   FStar_TypeChecker_Normalize.term_to_string goal.context
                     typ in
                 let uu____2722 =
                   FStar_TypeChecker_Normalize.term_to_string goal.context
                     goal.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2720 uu____2721 uu____2722 in
               try_unif uu____2706 uu____2717)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2731 =
      let is_unit_t t =
        let uu____2738 =
          let uu____2739 = FStar_Syntax_Subst.compress t in
          uu____2739.FStar_Syntax_Syntax.n in
        match uu____2738 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2743 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2753 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2753 with
           | (tm1,t,guard) ->
               let uu____2765 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2765 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2795 =
                         FStar_List.fold_left
                           (fun uu____2841  ->
                              fun uu____2842  ->
                                match (uu____2841, uu____2842) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2945 = is_unit_t b_t in
                                    if uu____2945
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2983 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____2983 with
                                       | (u,uu____3013,g_u) ->
                                           let uu____3027 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____3027,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2795 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3097 =
                             let uu____3106 =
                               let uu____3115 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3115.FStar_Syntax_Syntax.effect_args in
                             match uu____3106 with
                             | pre::post::uu____3126 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3167 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3097 with
                            | (pre,post) ->
                                let uu____3196 =
                                  let uu____3197 =
                                    let uu____3198 =
                                      FStar_Syntax_Util.mk_squash post in
                                    do_unify goal.context uu____3198
                                      goal.goal_ty in
                                  Prims.op_Negation uu____3197 in
                                if uu____3196
                                then
                                  let uu____3201 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.context tm1 in
                                  let uu____3202 =
                                    let uu____3203 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.context uu____3203 in
                                  let uu____3204 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.context goal.goal_ty in
                                  fail3
                                    "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                    uu____3201 uu____3202 uu____3204
                                else
                                  (let solution =
                                     FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                       FStar_Pervasives_Native.None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____3276  ->
                                             match uu____3276 with
                                             | (uu____3289,uu____3290,uu____3291,tm2,uu____3293,uu____3294)
                                                 ->
                                                 let uu____3295 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3295 with
                                                  | (hd1,uu____3311) ->
                                                      let uu____3332 =
                                                        let uu____3333 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3333.FStar_Syntax_Syntax.n in
                                                      (match uu____3332 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3336 -> true
                                                       | uu____3353 -> false)))) in
                                   let uu____3354 = solve goal solution in
                                   bind uu____3354
                                     (fun uu____3359  ->
                                        let uu____3360 =
                                          add_implicits implicits1 in
                                        bind uu____3360
                                          (fun uu____3371  ->
                                             let is_free_uvar uv t1 =
                                               let free_uvars =
                                                 let uu____3382 =
                                                   let uu____3389 =
                                                     FStar_Syntax_Free.uvars
                                                       t1 in
                                                   FStar_Util.set_elements
                                                     uu____3389 in
                                                 FStar_List.map
                                                   FStar_Pervasives_Native.fst
                                                   uu____3382 in
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
                                               let uu____3430 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t1 in
                                               match uu____3430 with
                                               | (hd1,uu____3446) ->
                                                   (match hd1.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_uvar
                                                        (uv,uu____3468) ->
                                                        appears uv goals
                                                    | uu____3493 -> false) in
                                             let sub_goals =
                                               FStar_All.pipe_right
                                                 implicits1
                                                 (FStar_List.map
                                                    (fun uu____3535  ->
                                                       match uu____3535 with
                                                       | (_msg,_env,_uvar,term,typ,uu____3553)
                                                           ->
                                                           let uu___111_3554
                                                             = goal in
                                                           let uu____3555 =
                                                             bnorm
                                                               goal.context
                                                               term in
                                                           let uu____3556 =
                                                             bnorm
                                                               goal.context
                                                               typ in
                                                           {
                                                             context =
                                                               (uu___111_3554.context);
                                                             witness =
                                                               uu____3555;
                                                             goal_ty =
                                                               uu____3556;
                                                             opts =
                                                               (uu___111_3554.opts);
                                                             is_guard =
                                                               (uu___111_3554.is_guard)
                                                           })) in
                                             let rec filter' f xs =
                                               match xs with
                                               | [] -> []
                                               | x::xs1 ->
                                                   let uu____3594 = f x xs1 in
                                                   if uu____3594
                                                   then
                                                     let uu____3597 =
                                                       filter' f xs1 in
                                                     x :: uu____3597
                                                   else filter' f xs1 in
                                             let sub_goals1 =
                                               filter'
                                                 (fun g  ->
                                                    fun goals  ->
                                                      let uu____3611 =
                                                        checkone g.witness
                                                          goals in
                                                      Prims.op_Negation
                                                        uu____3611) sub_goals in
                                             let uu____3612 =
                                               add_goal_from_guard
                                                 goal.context guard goal.opts in
                                             bind uu____3612
                                               (fun uu____3617  ->
                                                  let uu____3618 =
                                                    let uu____3621 =
                                                      let uu____3622 =
                                                        let uu____3623 =
                                                          FStar_Syntax_Util.mk_squash
                                                            pre in
                                                        istrivial
                                                          goal.context
                                                          uu____3623 in
                                                      Prims.op_Negation
                                                        uu____3622 in
                                                    if uu____3621
                                                    then
                                                      add_irrelevant_goal
                                                        goal.context pre
                                                        goal.opts
                                                    else ret () in
                                                  bind uu____3618
                                                    (fun uu____3628  ->
                                                       add_goals sub_goals1))))))))) in
    focus uu____2731
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3645 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3645 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3655::(e1,uu____3657)::(e2,uu____3659)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3718 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3741 = destruct_eq' typ in
    match uu____3741 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3771 = FStar_Syntax_Util.un_squash typ in
        (match uu____3771 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3804 =
           FStar_All.pipe_left mlog
             (fun uu____3814  ->
                let uu____3815 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3816 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3815
                  uu____3816) in
         bind uu____3804
           (fun uu____3824  ->
              let uu____3825 =
                let uu____3832 =
                  let uu____3833 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3833 in
                destruct_eq uu____3832 in
              match uu____3825 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3850 =
                    let uu____3851 = FStar_Syntax_Subst.compress x in
                    uu____3851.FStar_Syntax_Syntax.n in
                  (match uu____3850 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___112_3858 = goal in
                         let uu____3859 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3860 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___112_3858.context);
                           witness = uu____3859;
                           goal_ty = uu____3860;
                           opts = (uu___112_3858.opts);
                           is_guard = (uu___112_3858.is_guard)
                         } in
                       replace_cur goal1
                   | uu____3861 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3862 -> fail "Not an equality hypothesis"))
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
            let uu____3893 = FStar_TypeChecker_Env.pop_bv e in
            match uu____3893 with
            | FStar_Pervasives_Native.None  -> e
            | FStar_Pervasives_Native.Some (bv,e') ->
                if FStar_Syntax_Syntax.bv_eq bv b1
                then FStar_TypeChecker_Env.push_bv e' b2
                else
                  (let uu____3911 = alpha e' in
                   let uu____3912 =
                     let uu___113_3913 = bv in
                     let uu____3914 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___113_3913.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___113_3913.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3914
                     } in
                   FStar_TypeChecker_Env.push_bv uu____3911 uu____3912) in
          let c = alpha g.context in
          let w = FStar_Syntax_Subst.subst s g.witness in
          let t = FStar_Syntax_Subst.subst s g.goal_ty in
          let uu___114_3920 = g in
          {
            context = c;
            witness = w;
            goal_ty = t;
            opts = (uu___114_3920.opts);
            is_guard = (uu___114_3920.is_guard)
          }
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3941 = b in
           match uu____3941 with
           | (bv,uu____3945) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___115_3949 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___115_3949.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___115_3949.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3953 =
                   let uu____3954 =
                     let uu____3961 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3961) in
                   FStar_Syntax_Syntax.NT uu____3954 in
                 [uu____3953] in
               let uu____3962 = subst_goal bv bv' s1 goal in
               replace_cur uu____3962)
let rec find_bv_env:
  env ->
    FStar_Syntax_Syntax.bv ->
      (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.universe,
        env,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple6 tac
  =
  fun e  ->
    fun bv  ->
      let uu____4003 = FStar_TypeChecker_Env.pop_bv e in
      match uu____4003 with
      | FStar_Pervasives_Native.None  ->
          fail "binder_retype: binder is not present in environment"
      | FStar_Pervasives_Native.Some (bv',e') ->
          if FStar_Syntax_Syntax.bv_eq bv bv'
          then
            let uu____4066 =
              let uu____4073 = FStar_Syntax_Util.type_u () in
              match uu____4073 with | (ty,u) -> ret (ty, u) in
            bind uu____4066
              (fun uu____4112  ->
                 match uu____4112 with
                 | (ty,u) ->
                     let uu____4135 = new_uvar e' ty in
                     bind uu____4135
                       (fun t'  ->
                          let bv'' =
                            let uu___116_4157 = bv in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_4157.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_4157.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t'
                            } in
                          let uu____4158 =
                            let uu____4173 =
                              FStar_TypeChecker_Env.push_bv e' bv'' in
                            let uu____4174 =
                              let uu____4177 =
                                let uu____4178 =
                                  let uu____4185 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4185) in
                                FStar_Syntax_Syntax.NT uu____4178 in
                              [uu____4177] in
                            (e', ty, t', u, uu____4173, uu____4174) in
                          ret uu____4158))
          else
            (let uu____4203 = find_bv_env e' bv in
             bind uu____4203
               (fun uu____4257  ->
                  match uu____4257 with
                  | (e1,ty,t,u,e2,s) ->
                      let bv'1 =
                        let uu___117_4299 = bv' in
                        let uu____4300 =
                          FStar_Syntax_Subst.subst s
                            bv'.FStar_Syntax_Syntax.sort in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___117_4299.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___117_4299.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____4300
                        } in
                      let uu____4303 =
                        let uu____4318 =
                          FStar_TypeChecker_Env.push_bv e2 bv'1 in
                        (e1, ty, t, u, uu____4318, s) in
                      ret uu____4303))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4348 = b in
         match uu____4348 with
         | (bv,uu____4352) ->
             bind dismiss
               (fun uu____4355  ->
                  let uu____4356 = find_bv_env goal.context bv in
                  bind uu____4356
                    (fun uu____4395  ->
                       match uu____4395 with
                       | (env',ty,t',u,env,s) ->
                           let uu____4422 =
                             let uu____4425 =
                               let uu____4428 =
                                 let uu___118_4429 = goal in
                                 let uu____4430 =
                                   FStar_Syntax_Subst.subst s goal.witness in
                                 let uu____4431 =
                                   FStar_Syntax_Subst.subst s goal.goal_ty in
                                 {
                                   context = env;
                                   witness = uu____4430;
                                   goal_ty = uu____4431;
                                   opts = (uu___118_4429.opts);
                                   is_guard = (uu___118_4429.is_guard)
                                 } in
                               [uu____4428] in
                             add_goals uu____4425 in
                           bind uu____4422
                             (fun uu____4434  ->
                                let uu____4435 =
                                  FStar_Syntax_Util.mk_eq2
                                    (FStar_Syntax_Syntax.U_succ u) ty
                                    bv.FStar_Syntax_Syntax.sort t' in
                                add_irrelevant_goal env' uu____4435 goal.opts))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4441 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____4441 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4463 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4463 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___119_4497 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___119_4497.opts);
                is_guard = (uu___119_4497.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4509 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4509 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4530 = FStar_Syntax_Print.bv_to_string x in
               let uu____4531 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4530 uu____4531
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4538 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____4538 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____4560 = FStar_Util.set_mem x fns_ty in
           if uu____4560
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4564 = new_uvar env' goal.goal_ty in
              bind uu____4564
                (fun u  ->
                   let uu____4570 =
                     let uu____4571 = trysolve goal u in
                     Prims.op_Negation uu____4571 in
                   if uu____4570
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___120_4576 = goal in
                        let uu____4577 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____4577;
                          goal_ty = (uu___120_4576.goal_ty);
                          opts = (uu___120_4576.opts);
                          is_guard = (uu___120_4576.is_guard)
                        } in
                      bind dismiss (fun uu____4579  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4591 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4591 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4615  ->
                    let uu____4616 = clear b in
                    bind uu____4616
                      (fun uu____4620  ->
                         bind intro (fun uu____4622  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___121_4639 = g in
           {
             context = ctx';
             witness = (uu___121_4639.witness);
             goal_ty = (uu___121_4639.goal_ty);
             opts = (uu___121_4639.opts);
             is_guard = (uu___121_4639.is_guard)
           } in
         bind dismiss (fun uu____4641  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___122_4658 = g in
           {
             context = ctx';
             witness = (uu___122_4658.witness);
             goal_ty = (uu___122_4658.goal_ty);
             opts = (uu___122_4658.opts);
             is_guard = (uu___122_4658.is_guard)
           } in
         bind dismiss (fun uu____4660  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4702 = f x in
          bind uu____4702
            (fun y  ->
               let uu____4710 = mapM f xs in
               bind uu____4710 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4756 = FStar_Syntax_Subst.compress t in
          uu____4756.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4791 = ff hd1 in
              bind uu____4791
                (fun hd2  ->
                   let fa uu____4811 =
                     match uu____4811 with
                     | (a,q) ->
                         let uu____4824 = ff a in
                         bind uu____4824 (fun a1  -> ret (a1, q)) in
                   let uu____4837 = mapM fa args in
                   bind uu____4837
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4897 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4897 with
               | (bs1,t') ->
                   let uu____4906 =
                     let uu____4909 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4909 t' in
                   bind uu____4906
                     (fun t''  ->
                        let uu____4913 =
                          let uu____4914 =
                            let uu____4931 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4932 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4931, uu____4932, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4914 in
                        ret uu____4913))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4953 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___123_4957 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___123_4957.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___123_4957.FStar_Syntax_Syntax.vars)
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
            let uu____4986 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4986 with
            | (t1,lcomp,g) ->
                let uu____4998 =
                  let uu____4999 = FStar_TypeChecker_Rel.is_trivial g in
                  Prims.op_Negation uu____4999 in
                if uu____4998
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____5006 = new_uvar env typ in
                   bind uu____5006
                     (fun ut  ->
                        log ps
                          (fun uu____5017  ->
                             let uu____5018 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____5019 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____5018 uu____5019);
                        (let uu____5020 =
                           let uu____5023 =
                             let uu____5024 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____5024 typ t1 ut in
                           add_irrelevant_goal env uu____5023 opts in
                         bind uu____5020
                           (fun uu____5027  ->
                              let uu____5028 =
                                bind tau
                                  (fun uu____5033  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____5028))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____5054 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____5054 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____5091  ->
                   let uu____5092 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____5092);
              bind dismiss_all
                (fun uu____5095  ->
                   let uu____5096 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____5096
                     (fun gt'  ->
                        log ps
                          (fun uu____5106  ->
                             let uu____5107 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____5107);
                        (let uu____5108 = push_goals gs in
                         bind uu____5108
                           (fun uu____5112  ->
                              add_goals
                                [(let uu___124_5114 = g in
                                  {
                                    context = (uu___124_5114.context);
                                    witness = (uu___124_5114.witness);
                                    goal_ty = gt';
                                    opts = (uu___124_5114.opts);
                                    is_guard = (uu___124_5114.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5134 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____5134 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5146 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5146 with
            | (hd1,args) ->
                let uu____5179 =
                  let uu____5192 =
                    let uu____5193 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5193.FStar_Syntax_Syntax.n in
                  (uu____5192, args) in
                (match uu____5179 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5207::(l,uu____5209)::(r,uu____5211)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5258 =
                       let uu____5259 = do_unify g.context l r in
                       Prims.op_Negation uu____5259 in
                     if uu____5258
                     then
                       let uu____5262 =
                         FStar_TypeChecker_Normalize.term_to_string g.context
                           l in
                       let uu____5263 =
                         FStar_TypeChecker_Normalize.term_to_string g.context
                           r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5262 uu____5263
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5266) ->
                     let uu____5283 =
                       FStar_TypeChecker_Normalize.term_to_string g.context t in
                     fail1 "trefl: not an equality (%s)" uu____5283))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5291 = new_uvar g.context g.goal_ty in
       bind uu____5291
         (fun u  ->
            let g' =
              let uu___125_5298 = g in
              {
                context = (uu___125_5298.context);
                witness = u;
                goal_ty = (uu___125_5298.goal_ty);
                opts = (uu___125_5298.opts);
                is_guard = (uu___125_5298.is_guard)
              } in
            bind dismiss
              (fun uu____5301  ->
                 let uu____5302 =
                   let uu____5305 =
                     let uu____5306 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5306 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____5305 g.opts in
                 bind uu____5302
                   (fun uu____5309  ->
                      let uu____5310 = add_goals [g'] in
                      bind uu____5310 (fun uu____5314  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___126_5331 = ps in
              {
                main_context = (uu___126_5331.main_context);
                main_goal = (uu___126_5331.main_goal);
                all_implicits = (uu___126_5331.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___126_5331.smt_goals)
              })
       | uu____5332 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___127_5347 = ps in
              {
                main_context = (uu___127_5347.main_context);
                main_goal = (uu___127_5347.main_goal);
                all_implicits = (uu___127_5347.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___127_5347.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____5354 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5396 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____5396 with
         | (t1,typ,guard) ->
             let uu____5412 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5412 with
              | (hd1,args) ->
                  let uu____5455 =
                    let uu____5468 =
                      let uu____5469 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5469.FStar_Syntax_Syntax.n in
                    (uu____5468, args) in
                  (match uu____5455 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5488)::(q,uu____5490)::[]) when
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
                         let uu___128_5528 = g in
                         let uu____5529 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____5529;
                           witness = (uu___128_5528.witness);
                           goal_ty = (uu___128_5528.goal_ty);
                           opts = (uu___128_5528.opts);
                           is_guard = (uu___128_5528.is_guard)
                         } in
                       let g2 =
                         let uu___129_5531 = g in
                         let uu____5532 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____5532;
                           witness = (uu___129_5531.witness);
                           goal_ty = (uu___129_5531.goal_ty);
                           opts = (uu___129_5531.opts);
                           is_guard = (uu___129_5531.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5539  ->
                            let uu____5540 = add_goals [g1; g2] in
                            bind uu____5540
                              (fun uu____5549  ->
                                 let uu____5550 =
                                   let uu____5555 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5556 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5555, uu____5556) in
                                 ret uu____5550))
                   | uu____5561 ->
                       let uu____5574 =
                         FStar_TypeChecker_Normalize.term_to_string g.context
                           typ in
                       fail1 "Not a disjunction: %s" uu____5574)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5597 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5597);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___130_5604 = g in
                 {
                   context = (uu___130_5604.context);
                   witness = (uu___130_5604.witness);
                   goal_ty = (uu___130_5604.goal_ty);
                   opts = opts';
                   is_guard = (uu___130_5604.is_guard)
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
           let uu____5645 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____5645 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5674 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5680 =
              let uu____5681 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5681 in
            new_uvar env uu____5680 in
      bind uu____5674
        (fun typ  ->
           let uu____5693 = new_uvar env typ in
           bind uu____5693 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5713 = do_unify ps.main_context t1 t2 in ret uu____5713)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5733  ->
             let uu____5734 = FStar_Options.unsafe_tactic_exec () in
             if uu____5734
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5740  -> fun uu____5741  -> false) in
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
      let uu____5763 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5763 with
      | (u,uu____5781,g_u) ->
          let g =
            let uu____5796 = FStar_Options.peek () in
            {
              context = env;
              witness = u;
              goal_ty = typ;
              opts = uu____5796;
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
      let uu____5813 = goal_of_goal_ty env typ in
      match uu____5813 with
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